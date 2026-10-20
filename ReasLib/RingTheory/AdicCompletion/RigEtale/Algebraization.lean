module

public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.AdicCompletion.RigEtale
public import ReasLib.RingTheory.AdicCompletion.RigEtale.EtaleOverComplement

@[expose] public section

universe u

namespace Algebra.RigEtale

/-- A rig-étale algebra over a Noetherian pair `(A, I)` with principal ideal
`I` is isomorphic as an `A`-algebra to the completion of a finite type
`A`-algebra along the extension of `I`. -/
@[stacks 0ALS]
theorem exists_finiteTypeAlgEquiv_of_isPrincipal
    {A B : Type u} [CommRing A] [IsNoetherianRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) [I.IsPrincipal] [RigEtale I B] :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra A C)
      (_ : Algebra.FiniteType A C),
      Nonempty (AdicCompletion (I.map (algebraMap A C)) C ≃ₐ[A] B) :=
  sorry

/-- A rig-étale algebra over a Noetherian pair `(A, I)` is isomorphic as an
`A`-algebra to the completion of a finite type `A`-algebra along the extension
of `I`. -/
@[stacks 0AKA]
theorem exists_finiteTypeAlgEquiv
    {A B : Type u} [CommRing A] [IsNoetherianRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) [RigEtale I B] :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra A C)
      (_ : Algebra.FiniteType A C),
      Nonempty (AdicCompletion (I.map (algebraMap A C)) C ≃ₐ[A] B) :=
  sorry

/-- For a Noetherian ring `A`, an ideal `I`, and an `I`-adically complete
`A`-algebra `B` with finite type special fiber, `B` is rig-étale over `(A, I)`
if and only if it is the completion of a finite type `A`-algebra that is étale
over the complement of `V(I)`. -/
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

end Algebra.RigEtale
