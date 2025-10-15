# Outline

## Type System Design

- effect system for reification: Restrict the type of evaluation contexts affected by let-insertion.
- effect system for mutation：Τrack the side effects occurring in the first and second stages, as well as their interactions by run operator.
- code rep/fragment type: Determine whether a piece of code could be freely duplicated or discarded.

## Semantis Design

- fixpoint combinator
- let-insertion from POPL'18
- run operator for closed code

## Semantic Consistency

- let-insertion consistency
- substitution consistency
- partial evaluation under let𝕔
- commutative diagram of the proof

## Future Work

- extend to multi-stage
- other solutions for staging consistency
