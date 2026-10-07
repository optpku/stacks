module

public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
import StacksCheckRecall

@[expose] public section

/-!
Lemma 10.12.4: For `R`-modules `M₁, ..., Mᵣ`, the canonical multilinear map into their
tensor product has the universal factorization property, and the factorization is unique.

The canonical owner is `PiTensorProduct`: `tprod` is the universal multilinear map, `lift` is
the factorization equivalence, and `lift.unique` records uniqueness. These are the atomic
source-facing clauses; no chapter wrapper is needed.

@stack 00CZ
-/
@[stacks 00CZ "canonical multilinear map"]
#check @PiTensorProduct.tprod

@[stacks 00CZ "universal factorization"]
#check @PiTensorProduct.lift

@[stacks 00CZ "uniqueness of factorization"]
#check @PiTensorProduct.lift.unique
