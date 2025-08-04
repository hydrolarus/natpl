{
  pkgs,
  rustPlatform,
  version ? "0.1.0-git",
  ...
}:

rustPlatform.buildRustPackage {
  pname = "natpl";
  inherit version;
  src = ./.;
  cargoLock.lockFile = ./Cargo.lock;
  nativeBuildInputs = with pkgs; [
    pkg-config
    gnum4
  ];
  buildInputs = with pkgs; [
    mpfr
    gmp
  ];
}
