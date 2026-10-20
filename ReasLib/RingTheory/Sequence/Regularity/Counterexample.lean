module

public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Sequence.Koszul.Regularity

@[expose] public section

universe u

open IsLocalRing

namespace RingTheory.Sequence

/-- A commutative local ring can contain a regular sequence in its maximal ideal
whose first two entries annihilate a common nonzero element modulo the third. -/
theorem exists_isLocalRing_isRegular_quot_last_annihilated :
    ∃ (R : Type u) (_ : CommRing R) (_ : IsLocalRing R) (x y z : R),
      IsRegular R [x, y, z] ∧
        Ideal.ofList [x, y, z] ≤ maximalIdeal R ∧
        ∃ δ : R ⧸ Ideal.span {z}, δ ≠ 0 ∧ x • δ = 0 ∧ y • δ = 0 := sorry

/-- There exists a local homomorphism of commutative local rings with a regular pair
in the target's maximal ideal and a flat quotient by that pair over the base ring,
although the pair on the closed fiber is neither regular nor Koszul-regular. -/
@[stacks 0641]
theorem exists_isLocalHom_isRegular_flatQuotient_not_isKoszulRegular :
    ∃ (A B : Type u) (_ : CommRing A) (_ : CommRing B) (_ : IsLocalRing A) (_ : IsLocalRing B)
      (_ : Algebra A B) (_ : IsLocalHom (algebraMap A B)) (x y : B),
      let I := Ideal.map (algebraMap A B) (maximalIdeal A)
      let xbar := Ideal.Quotient.mk I x
      let ybar := Ideal.Quotient.mk I y
      IsRegular B [x, y] ∧
        Ideal.ofList [x, y] ≤ maximalIdeal B ∧
        Module.Flat A (B ⧸ Ideal.ofList [x, y]) ∧
        ¬ IsRegular (B ⧸ I) [xbar, ybar] ∧
        ¬ IsKoszulRegularSequence (Fin.cons xbar (Fin.cons ybar Fin.elim0)) := sorry

end RingTheory.Sequence
