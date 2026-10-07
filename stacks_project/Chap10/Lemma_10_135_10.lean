module

public import ReasLib.RingTheory.CompleteIntersection.OverField.FieldExtension
import StacksCheckRecall

/-!
# Complete intersections under field extension

@stack 00SI

The local complete-intersection predicate is owned by
`Algebra.IsCompleteIntersectionOver`.  This file retains its source-facing
invariance at corresponding primes after extending the ground field.
-/

@[expose] public section

/- Lemma 10.135.10 (00SI): let `K / k` be a field extension, let `S` be a
finite type `k`-algebra, and let `qK` be a prime of `K ⊗[k] S`.  The local ring
at the contracted prime is a complete intersection over `k` if and only if the
local ring at `qK` is a complete intersection over `K`. -/
@[stacks 00SI]
#check @Algebra.IsCompleteIntersectionOver.atPrime_iff_tensorProduct_fieldExtension
