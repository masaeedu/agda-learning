{ pkgs ? import <nixpkgs> {} }:

let
  ghc = pkgs.haskellPackages.ghcWithPackages (pkgs: with pkgs; [ ieee ]);

in

pkgs.mkShell {
  buildInputs = [ ghc ];
}
