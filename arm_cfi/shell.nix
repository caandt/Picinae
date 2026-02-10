{ pkgs ? import <nixpkgs> {} }:
  pkgs.mkShell {
    nativeBuildInputs = with pkgs.buildPackages; [
      pkgsCross.armv7l-hf-multiplatform.buildPackages.gcc
      ocamlPackages.domainslib
      ocamlPackages.findlib
      glibc.static
      (python3.withPackages (python-pkgs: [
        python-pkgs.lief
      ]))
    ];
}
