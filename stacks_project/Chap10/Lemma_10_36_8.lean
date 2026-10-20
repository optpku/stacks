module

public import ReasLib.RingTheory.IntegralClosure.Pi
import StacksCheckRecall

@[expose] public section

/-!
# Integrality in finite products

Lemma 10.36.8 (Tag 0CY8) recalls the reusable finite-product integrality owner.
@stack 0CY8
-/

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain triage:
* source-facing: integrality of an element in a finite product algebra.
* core/canonical owner: `IsIntegral`.
* bridge/view: `Polynomial.piEquiv`, the evaluation maps `Pi.evalRingHom`, and the binary owner
  theorem `IsIntegral.pair_iff`.
Primitive data remains exactly the witness polynomial from `IsIntegral`; the componentwise
criterion is derived API. -/

/- Lemma 10.36.8 is a canonical recall: the reusable declaration is owned by
`ReasLib.RingTheory.IntegralClosure.Pi`, so this chapter does not create a second
`IsIntegral.pi_iff` with the same name. -/
@[stacks 0CY8]
#check @IsIntegral.pi_iff
