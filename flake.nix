{
  description = "Sparkle HDL — reproducible development environment";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";

  outputs =
    { self, nixpkgs }:
    let
      # Linux-only: the RISC-V pkgsCross toolchains and the kernel build are
      # Linux-targeted.
      systems = [
        "x86_64-linux"
        "aarch64-linux"
      ];
      forAllSystems = f: nixpkgs.lib.genAttrs systems (system: f nixpkgs.legacyPackages.${system});
    in
    {
      # The CDC runner is standalone C++20 (std::thread / std::atomic) that
      # `JIT.runCDC` dlopen()s at runtime. It is built hermetically here rather
      # than linked, because static-linking it as a Lake extern_lib injects it
      # into the compile-time dynlib set and breaks `precompileModules`. The
      # `-march=native` from c_src/cdc/Makefile is dropped for reproducibility.
      packages = forAllSystems (pkgs: {
        cdc-runner = pkgs.stdenv.mkDerivation {
          pname = "sparkle-cdc-runner";
          version = "0.1.0";
          src = ./c_src/cdc;
          buildPhase = ''
            $CXX -std=c++20 -O3 -pthread -shared -fPIC -o cdc_runner.so cdc_runner.cpp
          '';
          installPhase = ''
            mkdir -p $out/lib
            cp cdc_runner.so $out/lib/
          '';
        };
      });

      # Reproducibility boundary: everything below is pinned by flake.lock.
      # Lean itself is *not* — `elan` reads `lean-toolchain` and fetches v4.28.0
      # at runtime, and `lake` fetches the deps pinned in `lake-manifest.json`.
      # Reproducible by pin, not hermetic.
      devShells = forAllSystems (pkgs: {
        default = pkgs.mkShell {
          name = "sparkle-dev-shell";

          # Deterministic, declarative discovery of the CDC runner: the FFI's
          # ensure_cdc_runner() (c_src/sparkle_jit.c) dlopen()s this path first.
          # Set as an env attribute (not a shellHook) so every shell entry is
          # identical and has no filesystem side effects.
          SPARKLE_CDC_RUNNER_SO = "${self.packages.${pkgs.stdenv.hostPlatform.system}.cdc-runner}/lib/cdc_runner.so";

          buildInputs = with pkgs; [
            # Lean toolchain manager. Resolves the `lean-toolchain` pin (v4.28.0)
            # and provides `lake`. Lean is fetched at runtime, not from nix.
            elan

            # The JIT simulator codegens C++ and compiles it at runtime via
            # `c++`. stdenv already provides a compiler; listed for intent.
            gcc

            # Simulation / synthesis backends.
            verilator
            iverilog # Icarus Verilog for quick simulations
            yosys

            pkg-config
            cmake
            (python3.withPackages (
              ps: with ps; [
                numpy
                matplotlib
                pyyaml
                pandas
                pip
                jupytext
                nbconvert
                jupyterlab
              ]
            ))
            nodejs

            # RISC-V cross-toolchains for the RV32 SoC firmware and Linux image.
            pkgsCross.riscv32-embedded.buildPackages.gcc
            pkgsCross.riscv32-embedded.buildPackages.binutils
            pkgsCross.riscv64.buildPackages.gcc
            pkgsCross.riscv64.buildPackages.binutils

            # Device-tree compiler — turns sparkle-soc.dts into the .dtb that
            # OpenSBI hands to Linux at boot.
            dtc

            # Kernel build prerequisites.
            bc
            flex
            bison
            openssl
            cpio
            gzip
            nlohmann_json
            libuuid
            zstd.dev
          ];

          shellHook = ''
            echo "--- Sparkle HDL Development Environment ---"
            echo "Verilator: $(verilator --version)"
            echo "elan:      $(elan --version)"
            echo "-------------------------------------------"

            export VERILATOR_ROOT=${pkgs.verilator}/share/verilator
          '';
        };
      });

      formatter = forAllSystems (pkgs: pkgs.nixfmt);
    };
}
