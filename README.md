# Autosubst 2 

*This is the `main` branch containing the development version of Autosubst 2. We recommend using the `main` branch in almost every case, since it exceeds the released beta versions in functionality and usability.*

Formalizing syntactic theories with variable binders in a general-purpose proof assistant is hard.

With Autosubst 2, we present a tool that:

1. offers support for unscoped and well-scoped de Bruijn in Coq.
2. generates first-order renaming, substitutions, and the appropriate substitution lemmas.
3. offers support for custom syntax: potentially mutually inductive and with several sorts of variables.

## Requirements:

- [Haskell Stack build environment](https://docs.haskellstack.org/en/stable/README/ "The Haskell Tool Stack")
- active internet connection (stack setup loads and installs a private version of GHC)
- the generated output is compatible with Coq 8.11.

## Installation

```
stack setup
stack init
stack build
stack exec -- as2-exe <OPTIONS>
```

You can use ```stack install```, to later on use ```as2-exe``` instead of ```stack exec --as2-exe```.

## Summary

With no options, Autosubst 2 operates as follows:

1. reads a HOAS specification from stdin
2. prints generated well-scoped Coq code to stdout

See the ``signatures`` file system for examples of the HOAS specification.

In the standard case, a user probably wants to specify input and output files via the ``-i`` and ``-o`` option. The following command generates the code for a call-by-value variant of System F and dumps it to `sysf_cbv.v`. 

```
stack exec -- as2-exe -i specs/sysf_cbv.sig -o sysf_cbv.v
```

The generated code depends on a small number of header files which define commonly used notations and definitions. These library files are called ``axioms.v`` (needed for all output, imports e.g. functional extensionality), ``fintype.v`` (only for well-scoped syntax),  ``unscoped.v`` (for unscoped syntax), and ``header_extensible.v`` (for modular syntax) and can be found in the headers directory.

To use the generated code, place the output of the tool, say ``syntax.v``,  and the respective header file in your project directory, and import them by adding the following directive to your development (the header is sourced implicitly through the generated code file):

```
Require Export syntax.
```

### Options

Per default, the tool will not silently overwrite existing files but request for user confirmation. This can be explicitly disabled via the ``-f`` option. The maximal line width of the generated Coq code is 140 characters, but this can also be adjusted via the ``-w`` option.

It is furthermore possible to choose for which prover code is generated.
At the moment, *well-scoped Coq* code (``-p Coq``), *unscoped Coq* code (``-p UCoq``), and output for *only modular syntax* (``-p ECoq``) (see [modexp.sig](signatures/modexp.sig)) are available.
Not all modes are compatible with all syntactic inputs and the tool will output a corresponding error message.

The following command prints an overview of all options:

```
stack exec -- as2-exe --help
```

## Bugs, Requests, etc.

Please direct any inquiries regarding this software via Github.

## Other Implementations 
This main branch contains the development version of Autosubst 2 implemented in Haskell as described in the referred publications. 

An independent implementation of Autosubst 2 in OCaml developed by Adrian Dapprich is available at https://github.com/uds-psl/autosubst-ocaml. This implementation can be installed via ``opam`` and does not support modular syntax.

Another independent implementation of Autosusbt 2 in MetaCoq is available at https://github.com/uds-psl/autosubst-metacoq. It can be used as a command from within Coq, but for now remains a proof of concept with some missing features.

## Publications

- **[Mechanising Syntax with Binders in Coq](https://www.ps.uni-saarland.de/Publications/details/Stark:2020:Mechanising.html)**  [*(pdf)*](https://www.ps.uni-saarland.de/Publications/documents/Stark_2020_Mechanising.pdf) [*(Code)*](https://github.com/uds-psl/autosubst2/tree/v0.2-beta)
  *[Kathrin Stark](https://www.ps.uni-saarland.de/Publications/list/Kathrin_Stark.html)*
  PhD Thesis, Saarland University
- **[Coq à la Carte - A Practical Approach to Modular Syntax with Binders](https://www.ps.uni-saarland.de/Publications/details/ForsterStark:2020:Coq.html)**  [*(pdf)*](https://www.ps.uni-saarland.de/Publications/documents/ForsterStark_2020_Coq.pdf) [*(Code)*](https://github.com/uds-psl/coq-a-la-carte-cpp20)
  *[Yannick Forster](https://www.ps.uni-saarland.de/Publications/list/Yannick_Forster.html), [Kathrin Stark](https://www.ps.uni-saarland.de/Publications/list/Kathrin_Stark.html)*
  9th ACM SIGPLAN International Conference on Certified Programs and Proofs, CPP 2020, New Orleans, USA
- **[Autosubst 2: Reasoning with Multi-Sorted de Bruijn Terms and Vector Substitutions](https://www.ps.uni-saarland.de/Publications/details/StarkEtAl:2018:Autosubst-2:.html)**  [*(pdf)*](https://www.ps.uni-saarland.de/Publications/documents/StarkEtAl_2018_Autosubst-2_.pdf) [*(Code)*](https://github.com/uds-psl/autosubst2/tree/v0.1-beta)
  *[Kathrin Stark](https://www.ps.uni-saarland.de/Publications/list/Kathrin_Stark.html), [Steven Schäfer](https://www.ps.uni-saarland.de/Publications/list/Steven_Schäfer.html), [Jonas Kaiser](https://www.ps.uni-saarland.de/Publications/list/Jonas_Kaiser.html)* 
  8th ACM SIGPLAN International Conference on Certified Programs and Proofs, CPP 2019, Cascais, Portugal, January 14-15, 2019
- **[Autosubst 2: Towards Reasoning with Multi-Sorted de Bruijn Terms and Vector Substitutions](https://www.ps.uni-saarland.de/Publications/details/KaiserSchaeferStark:2017:Autosubst-2:.html)** [*(pdf)*](https://www.ps.uni-saarland.de/Publications/documents/KaiserSchaeferStark_2017_Autosubst-2_.pdf)
  *[Jonas Kaiser](https://www.ps.uni-saarland.de/Publications/list/Jonas_Kaiser.html), [Steven Schäfer](https://www.ps.uni-saarland.de/Publications/list/Steven_Schäfer.html), [Kathrin Stark](https://www.ps.uni-saarland.de/Publications/list/Kathrin_Stark.html)*
  LFMTP 2018
