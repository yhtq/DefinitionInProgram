{ pkgs, nixpkgs }:

let
  metadata = builtins.fromJSON (builtins.readFile ./lean-toolchain.json);
  lib = pkgs.lib;

  fetchSource =
    spec:
    pkgs.fetchFromGitHub (
      {
        owner = spec.owner;
        repo = spec.repo;
        hash = spec.hash;
      }
      // (if spec ? tag then { tag = spec.tag; } else { rev = spec.rev; })
    );

  lean4PackageFile = "${nixpkgs.outPath}/pkgs/development/lean-modules/lean4";
  mimallocSource = fetchSource metadata.lean.mimalloc;

  # The nixpkgs leanPackages definition keeps the compiler derivation private
  # inside its wrapper. Evaluate that same definition with a small test
  # symlinkJoin which returns its first path, exposing the unwrapped compiler
  # without using pkgs.lean4 as a second toolchain.
  lean4UnwrappedBase = pkgs.callPackage lean4PackageFile {
    symlinkJoin = args: builtins.head args.paths;
    fetchFromGitHub =
      args:
      if args.owner == metadata.lean.owner && args.repo == metadata.lean.repo then
        fetchSource metadata.lean
      else
        pkgs.fetchFromGitHub args;
  };

  lean4Unwrapped = lean4UnwrappedBase.overrideAttrs (_old: {
    version = metadata.lean.version;
    src = fetchSource metadata.lean;
    mimalloc-src = mimallocSource;
    buildInputs = (_old.buildInputs or [ ]) ++ [ pkgs.openssl ];
    cmakeFlags =
      (_old.cmakeFlags or [ ])
      ++ [ "-DCMAKE_INTERPROCEDURAL_OPTIMIZATION=ON" ]
      ++ lib.optionals pkgs.stdenv.cc.isGNU [
        # Nix's CMake hook selects plain Binutils by default. Build indexed,
        # fat GCC LTO archives: Lean's own links still optimize the IR, while
        # downstream Lake executables can consume the native fallback without
        # having to enable LTO or use an exactly matching compiler plugin.
        "-DCMAKE_AR=${pkgs.stdenv.cc.cc}/bin/gcc-ar"
        "-DCMAKE_RANLIB=${pkgs.stdenv.cc.cc}/bin/gcc-ranlib"
        "-DCMAKE_NM=${pkgs.stdenv.cc.cc}/bin/gcc-nm"
      ];

    # Lean 4.34 added GIT_BRANCH and a default SOURCE_DIR to the mimalloc
    # FetchContent declaration. The nixpkgs patch still handles the vendored
    # source, but its old replacement must also remove these two fields.
    postPatch =
      let
        pattern = "\${LEAN_BINARY_DIR}/../mimalloc/src/mimalloc";
      in
      ''
        substituteInPlace src/CMakeLists.txt \
          --replace-fail 'set(GIT_SHA1 "")' 'set(GIT_SHA1 "${metadata.lean.tag}")'

        rm -rf src/lake/examples/git/

        for file in stage0/src/CMakeLists.txt src/CMakeLists.txt; do
          substituteInPlace "$file" \
            --replace-fail \
              'project(LEAN CXX C)' \
              'project(LEAN CXX C)
        if(CMAKE_CXX_COMPILER_ID STREQUAL "GNU")
          foreach(lang C CXX)
            list(REMOVE_ITEM CMAKE_''${lang}_COMPILE_OPTIONS_IPO -fno-fat-lto-objects)
            list(APPEND CMAKE_''${lang}_COMPILE_OPTIONS_IPO -ffat-lto-objects)
          endforeach()
        endif()'
        done

        sed -i \
          -e '/GIT_BRANCH dev3/d' \
          -e '/^[[:space:]]*SOURCE_DIR[[:space:]]*$/,+1d' \
          CMakeLists.txt
        substituteInPlace CMakeLists.txt \
          --replace-fail 'GIT_REPOSITORY https://github.com/microsoft/mimalloc' \
                         'SOURCE_DIR "${mimallocSource}"' \
          --replace-fail 'GIT_TAG ${metadata.lean.mimalloc.tag}' ""

        for file in stage0/src/CMakeLists.txt stage0/src/runtime/CMakeLists.txt src/CMakeLists.txt src/runtime/CMakeLists.txt; do
          substituteInPlace "$file" \
            --replace-fail '${pattern}' '${mimallocSource}'
        done

        substituteInPlace src/lake/Lake/Load/Lean/Elab.lean \
          --replace-fail \
            'let upToDate := (← olean.pathExists) ∧' \
            'let upToDate := cfg.pkgDir.toString.startsWith "/nix/store/" ∨ (← olean.pathExists) ∧'
      '';
  });

  lean4 = pkgs.symlinkJoin {
    pname = "lean4";
    version = metadata.lean.version;
    name = "lean4-${metadata.lean.version}";
    paths = [ lean4Unwrapped ] ++ (builtins.tail pkgs.leanPackages.lean4.paths);
    nativeBuildInputs = [ pkgs.perl ];
    inherit (lean4Unwrapped) src meta;

    # nixpkgs patches the compiler's embedded store path when it creates the
    # wrapper. Without this, Lean's runtime lookup can point at the unwrapped
    # compiler's immutable store path.
    postBuild = ''
      oldStorePath=$(echo ${lean4Unwrapped} | ${pkgs.coreutils}/bin/head -c 43)
      newStorePath=$(echo "$out" | ${pkgs.coreutils}/bin/head -c 43)

      for bin in ${lean4Unwrapped}/bin/*; do
        test -f "$bin" || continue
        ${pkgs.coreutils}/bin/install -m755 "$bin" "$out/bin/"
        ${pkgs.perl}/bin/perl -pi -e "s|\Q$oldStorePath\E|$newStorePath|g" "$out/bin/$(basename "$bin")"
      done
    '';

    passthru = {
      inherit (lean4Unwrapped) src version;
    };
  };

  packageFiles = {
    lean4 = lean4PackageFile;
    batteries = "${nixpkgs.outPath}/pkgs/development/lean-modules/batteries";
    aesop = "${nixpkgs.outPath}/pkgs/development/lean-modules/aesop";
    Qq = "${nixpkgs.outPath}/pkgs/development/lean-modules/Qq";
    proofwidgets = "${nixpkgs.outPath}/pkgs/development/lean-modules/proofwidgets";
    plausible = "${nixpkgs.outPath}/pkgs/development/lean-modules/plausible";
    LeanSearchClient = "${nixpkgs.outPath}/pkgs/development/lean-modules/LeanSearchClient";
    Cli = "${nixpkgs.outPath}/pkgs/development/lean-modules/Cli";
    importGraph = "${nixpkgs.outPath}/pkgs/development/lean-modules/importGraph";
    mathlib = "${nixpkgs.outPath}/pkgs/development/lean-modules/mathlib";
  };

  proofwidgetsNpmDeps = pkgs.fetchNpmDeps {
    name = "lean4-proofwidgets-npm-deps";
    src = fetchSource metadata.packages.proofwidgets;
    sourceRoot = "source/widget";
    hash = metadata.packages.proofwidgets.npmHash;
  };

  # Bind nixpkgs' Lake builder to the compiler above. Package definitions are
  # then evaluated again inside the overridden scope, so their native compiler
  # and transitive Lean dependencies are not stale nixpkgs derivations.
  baseBuildLakePackage = pkgs.callPackage "${nixpkgs.outPath}/pkgs/build-support/lake" {
    lean4 = lean4;
  };

  buildLakePackage =
    argsOrFunction:
    baseBuildLakePackage (
      finalAttrs:
      let
        attrs = if builtins.isFunction argsOrFunction then argsOrFunction finalAttrs else argsOrFunction;
        packageName = attrs.leanPackageName or null;
        spec = if packageName == null then null else metadata.packages.${packageName} or null;
      in
      attrs
      // lib.optionalAttrs (spec != null) (
        {
          version = spec.version;
          src = fetchSource spec;
        }
        // lib.optionalAttrs (packageName == "proofwidgets") {
          npmDeps = proofwidgetsNpmDeps;
        }
      )
    );

  leanPackages = pkgs.leanPackages.overrideScope (
    final: _previous: {
      inherit lean4 buildLakePackage;

      batteries = final.callPackage packageFiles.batteries {
        inherit buildLakePackage;
      };
      aesop = final.callPackage packageFiles.aesop {
        inherit buildLakePackage;
      };
      Qq = final.callPackage packageFiles.Qq {
        inherit buildLakePackage;
      };
      proofwidgets = final.callPackage packageFiles.proofwidgets {
        inherit buildLakePackage;
      };
      plausible = final.callPackage packageFiles.plausible {
        inherit buildLakePackage;
      };
      LeanSearchClient = final.callPackage packageFiles.LeanSearchClient {
        inherit buildLakePackage;
      };
      Cli = final.callPackage packageFiles.Cli {
        inherit buildLakePackage;
      };
      importGraph = final.callPackage packageFiles.importGraph {
        inherit buildLakePackage;
      };
      mathlib = final.callPackage packageFiles.mathlib {
        inherit buildLakePackage;
      };

      # This alias is part of nixpkgs' public leanPackages interface.
      mathlib__archive = final.mathlib.passthru.mathlib__archive;
    }
  );
in
{
  inherit
    metadata
    lean4
    leanPackages
    proofwidgetsNpmDeps
    ;
}
