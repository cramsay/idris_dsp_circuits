{ nixpkgs ? import <nixpkgs> {} }:

with nixpkgs;

mkShell {
  name = "idris-shell";
  buildInputs = [
    idris
  ];
}
