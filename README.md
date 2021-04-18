# On Applications of Dependent Types to Parameterised Digital Signal Processing Circuits

The home of the source files accompanying the paper "On
Applications of Dependent Types to Parameterised Digital Signal Processing
Circuits". We present an *experimental* circuit simulation library for Idrs, a
lovely functional language with dependent types.

The main examples are:

  1. An FIR with minimal bit growth (both signed and unsigned)
  2. A CIC filter with Hogenauer's register pruning strategy

Idris sources and a Nix shell description are in `src/`. For example, the unsigned FIR demonstration can be run with:

```console
sdr@strath:~/repo$ cd src/
sdr@strath:~/repo/src$ nix-shell
sdr@strath:~/repo/src$ idris FirUnsigned.idr
     ____    __     _
    /  _/___/ /____(_)____
    / // __  / ___/ / ___/     Version 1.3.3-git:PRE
  _/ // /_/ / /  / (__  )      https://www.idris-lang.org/
 /___/\__,_/_/  /_/____/       Type :? for help

Idris is free software with ABSOLUTELY NO WARRANTY.
For details type :warranty.
*FirUnsigned> :exec main
```

The nix package manager (used here to encourage reproducibility) is a dependency of this project. To install it on any Linux distribution, MacOS, or Windows (via WSL), visit [their homepage](https://nixos.org/guides/install-nix.html) or run the following command if you're a trusting type:

```console
sdr@strath:~/$ https://nixos.org/guides/install-nix.html
```

## License

[BSD 3-clause](./LICENSE)
