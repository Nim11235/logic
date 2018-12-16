# ProofChecker
Library for checking formally constructed proofs.

# Usage
## What This Library Has:
Objects and classes representing Formlae and deductive steps. It also
provides the necessary interfaces required to fully check a mathematical
proof.

## What This Library Does Not Have:
This library is not an automated proving system: Proofs must be
constructed either by hand or by some other system, and 
knoweledge bases required for checking proofs are maintained by
the client.

# Examples:
A number of examples exist in the [theorems][1] modules, which demonstrate
an "in-software" implementation of some proofs. Some examples:

## Equality:
See [here][3] for proofs of some standard properties of equality.

## DeMorgan's Law:
See [here][2], where an in-software theorem and proof are constructed for 
one part of DeMorgan's Law.

[1]: https://github.com/Nim11235/logic/tree/master/src/theorems
[2]: https://github.com/Nim11235/logic/blob/master/src/theorems/de_morgan.rs
[3]: https://github.com/Nim11235/logic/blob/master/src/theorems/equality.rs