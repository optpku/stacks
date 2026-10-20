module

public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Finiteness.Defs
public import ReasLib.RingTheory.Etale.WContractible

@[expose] public section

universe u v

namespace IsWContractibleRing

/-- A finite finitely presented algebra over a w-contractible ring is w-contractible. -/
theorem ofFinite_finitePresentation (A : Type u) {B : Type v}
    [CommRing A] [CommRing B] [Algebra A B] [IsWContractibleRing A]
    [Module.Finite A B] [Algebra.FinitePresentation A B] :
    IsWContractibleRing B := by
  sorry

/-- A finite finitely presented ring homomorphism out of a w-contractible ring has
w-contractible target. -/
theorem of_ringHom {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    {f : A →+* B} (hfin : f.Finite) (hfp : f.FinitePresentation)
    [IsWContractibleRing A] : IsWContractibleRing B :=
  sorry

end IsWContractibleRing
