module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap88.Definition_88_18_1_Ring

@[expose] public section

universe u

namespace Algebra.RigSmooth

/-- Remark 88.7.3: Let `I` be an ideal of a Noetherian ring `A`. Let `B` be an
object of (88.2.0.2) which is rig-smooth over `(A, I)`. Then `B` is
`A`-algebra isomorphic to the `I`-adic completion of a finite type `A`-algebra
(Gabber–Zavyalov Theorem 1.2). This supercedes `exists_finiteTypeAlgEquiv`
(Proposition 88.6.3), `Algebra.RigEtale.exists_finiteTypeAlgEquiv`
(Lemma 88.10.2), and Elkik III Theorem 7 when `I` is principal. -/
@[stacks 0GAX]
theorem exists_finiteTypeAlgEquiv_of_isNoetherianRing
    {A B : Type u} [CommRing A] [IsNoetherianRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) [RigSmooth I B] :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra A C)
      (_ : Algebra.FiniteType A C),
      Nonempty (AdicCompletion (I.map (algebraMap A C)) C ≃ₐ[A] B) :=
  sorry

end Algebra.RigSmooth
