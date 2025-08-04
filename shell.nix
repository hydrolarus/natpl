{
  pkgs ? import <nixpkgs> {},
  ...
}:

pkgs.mkShell {
  nativeBuildInputs = with pkgs; [
    rustc
    cargo
    rustfmt
    clippy
    rust-analyzer
    pkg-config
    gnum4
  ];
  buildInputs = with pkgs; [
    mpfr.dev
    gmp.dev
  ];
}
