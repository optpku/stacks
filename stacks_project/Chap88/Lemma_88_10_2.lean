module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap88.Definition_88_20_1_Ring

@[expose] public section

universe u

namespace Algebra.RigEtale

/-- Lemma 88.10.2: Let `A` be a Noetherian ring and `I ⊂ A` an ideal. Let `B`
be an object of (88.2.0.2) which is rig-étale over `(A, I)`. Then there
exists a finite type `A`-algebra `C` and an `A`-algebra isomorphism
`B ≃ₐ[A] C^∧`, where `C^∧` is `AdicCompletion (I.map (algebraMap A C)) C`. -/
@[stacks 0AKA]
theorem exists_finiteTypeAlgEquiv
    {A B : Type u} [CommRing A] [IsNoetherianRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) [RigEtale I B] :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra A C)
      (_ : Algebra.FiniteType A C),
      Nonempty (AdicCompletion (I.map (algebraMap A C)) C ≃ₐ[A] B) :=
  sorry

end Algebra.RigEtale
