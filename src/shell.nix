{ nixpkgs ? import <nixpkgs> {} }:

with nixpkgs;

mkShell {
  name = "idris-shell";
  buildInputs = [
    (idrisPackages.with-packages (with idrisPackages; [ contrib pruviloj ]))
  ];
}
