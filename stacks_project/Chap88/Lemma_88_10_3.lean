module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap88.Definition_88_20_1_Ring
public import stacks_project.Chap88.Lemma_88_8_4_EtaleOverComplement

@[expose] public section

universe u

namespace Algebra.RigEtale

/-- Lemma 88.10.3: Let `A` be a Noetherian ring, `I ⊂ A` an ideal, and `B` an
object of (88.2.0.2), i.e. `TopologicallyFiniteType I B`. The equivalent
conditions of Lemma 88.8.2 are also equivalent to the existence of a finite
type `A`-algebra `C` such that `IsEtaleOverComplement I C` (so
`Spec(C) → Spec(A)` is étale over `Spec(A) \ V(I)`) and
`Nonempty (AdicCompletion (I.map (algebraMap A C)) C ≃ₐ[A] B)`. This is the
extra TFAE clause (8) for `RigEtale I B`. -/
@[stacks 0AKG]
theorem iff_exists_finiteType_isEtaleOverComplement
    {A B : Type u} [CommRing A] [IsNoetherianRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) [TopologicallyFiniteType I B] :
    RigEtale I B ↔
      ∃ (C : Type u) (_ : CommRing C) (_ : Algebra A C)
        (_ : Algebra.FiniteType A C),
        IsEtaleOverComplement I C ∧
          Nonempty (AdicCompletion (I.map (algebraMap A C)) C ≃ₐ[A] B) :=
  sorry

/-- A rig-étale algebra over `(A, I)` is isomorphic to the `I`-adic completion
of some finite type `A`-algebra étale over `Spec(A) \ V(I)`. -/
theorem exists_finiteType_isEtaleOverComplement
    {A B : Type u} [CommRing A] [IsNoetherianRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) [RigEtale I B] :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra A C)
      (_ : Algebra.FiniteType A C),
      IsEtaleOverComplement I C ∧
        Nonempty (AdicCompletion (I.map (algebraMap A C)) C ≃ₐ[A] B) :=
  sorry

/-- An object of (88.2.0.2) isomorphic to the `I`-adic completion of a finite
type `A`-algebra étale over `Spec(A) \ V(I)` is rig-étale over `(A, I)`. -/
theorem of_exists_finiteType_isEtaleOverComplement
    {A B : Type u} [CommRing A] [IsNoetherianRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) [TopologicallyFiniteType I B]
    (h : ∃ (C : Type u) (_ : CommRing C) (_ : Algebra A C)
      (_ : Algebra.FiniteType A C),
      IsEtaleOverComplement I C ∧
        Nonempty (AdicCompletion (I.map (algebraMap A C)) C ≃ₐ[A] B)) :
    RigEtale I B :=
  sorry

end Algebra.RigEtale
