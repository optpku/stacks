/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Finiteness.Defs
public import ReasLib.RingTheory.Henselian.PairHenselization

@[expose] public section

universe u v w

namespace IsPairHenselization

/-- A quotient of the henselization of a finite type algebra over a Noetherian
ring has an adic completion equivalent to that of a finite type algebra. -/
theorem exists_finiteTypeAlgEquiv_quotient
    {A : Type u} {C : Type v} {Ch : Type w}
    [CommRing A] [IsNoetherianRing A] [CommRing C] [CommRing Ch]
    [Algebra A C] [Algebra A Ch] [Algebra C Ch] [IsScalarTower A C Ch]
    [Algebra.FiniteType A C]
    (I : Ideal A) (Ih : Ideal Ch) (J : Ideal Ch)
    [IsPairHenselization C (Ideal.map (algebraMap A C) I) Ch Ih] :
    ∃ (B : Type (max u v w)) (_ : CommRing B) (_ : Algebra A B)
      (_ : Algebra.FiniteType A B),
      Nonempty
        (AdicCompletion (Ideal.map (algebraMap A B) I) B ≃ₐ[A]
          AdicCompletion (Ideal.map (algebraMap A (Ch ⧸ J)) I) (Ch ⧸ J)) := sorry

end IsPairHenselization
