# Cl-Aim

This is an experiment with declarative theorem provers. After LaTTe
showed it could be done in Lisp, I wondered if it was possible to
tinker around with different foundations.

The goal is to examine to what degree we can abstract away the
foundations of mathematics. Is it possible to generically work with
"objects" and some sense of "type" in a loose sense of the word?
Specifically, can we form proofs using the interface, and never think
about the foundations ever again?

I'm going to try to implement at least two theorem provers (one based on
Mizar-like syntax and set theory, the other based on some suitably
strong type theory). If ever I feel bored, I may try to implement a
higher-order logic prover.
