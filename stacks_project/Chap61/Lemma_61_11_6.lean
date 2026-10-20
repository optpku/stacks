module

public import ReasLib.RingTheory.Etale.WContractible.FinitePresentation
import StacksCheckRecall

@[expose] public section

universe u v

/- Lemma 61.11.6: if `A → B` is a finite and finitely presented ring map and
`A` is w-contractible, then `B` is w-contractible. -/
@[stacks 0986] #check (IsWContractibleRing.ofFinite_finitePresentation :
  ∀ (A : Type u) {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [IsWContractibleRing A] [Module.Finite A B] [Algebra.FinitePresentation A B],
    IsWContractibleRing B)

/- A finite finitely presented ring hom out of a w-contractible ring has
w-contractible target. -/
#check (IsWContractibleRing.of_ringHom :
  ∀ {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    {f : A →+* B} (_ : f.Finite) (_ : f.FinitePresentation)
    [IsWContractibleRing A], IsWContractibleRing B)
