module

public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap61.Definition_61_11_1_WContractible

@[expose] public section

universe u v

namespace IsWContractibleRing

set_option synthInstance.checkSynthOrder false in
/-- Lemma 61.11.6: if `A → B` is a finite and finitely presented ring map and
`A` is w-contractible, then `B` is w-contractible. -/
@[stacks 0986, instance]
instance ofFinite_finitePresentation {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [Algebra A B] [IsWContractibleRing A]
    [Module.Finite A B] [Algebra.FinitePresentation A B] :
    IsWContractibleRing B :=
  sorry

/-- A finite finitely presented ring hom out of a w-contractible ring has
w-contractible target. -/
theorem of_ringHom {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    {f : A →+* B} (hfin : f.Finite) (hfp : f.FinitePresentation)
    [IsWContractibleRing A] : IsWContractibleRing B :=
  sorry

end IsWContractibleRing
