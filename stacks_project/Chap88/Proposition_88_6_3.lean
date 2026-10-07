module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Regular.GRing
public import stacks_project.Chap88.Definition_88_18_1_Ring

/-!
# Algebraization of rig-smooth algebras over G-rings

A rig-smooth algebra over a Noetherian G-ring is isomorphic to the `I`-adic
completion of a finite type algebra.
-/

@[expose] public section

universe u

namespace Algebra.RigSmooth

/-- Proposition 88.6.3: Let `I` be an ideal of a Noetherian G-ring `A`. Let
`B` be an object of (88.2.0.2), i.e. an `A`-algebra which is
`Algebra.TopologicallyFiniteType I B`. If `B` is rig-smooth over `(A, I)`,
then there exists a finite type `A`-algebra `C` and an `A`-algebra
isomorphism `B ≃ₐ[A] C^∧`, where `C^∧` is
`AdicCompletion (I.map (algebraMap A C)) C`. -/
@[stacks 0GAT]
theorem exists_finiteTypeAlgEquiv
    {A B : Type u} [CommRing A] [IsGRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) [RigSmooth I B] :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra A C)
      (_ : Algebra.FiniteType A C),
      Nonempty (AdicCompletion (I.map (algebraMap A C)) C ≃ₐ[A] B) :=
  sorry

end Algebra.RigSmooth
