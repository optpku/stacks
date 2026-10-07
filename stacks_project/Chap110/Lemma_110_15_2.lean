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

/-- Lemma 110.15.2: there exists a local homomorphism of local rings `algebraMap A B` and a
regular sequence `x`, `y` in `maximalIdeal B` such that `B ⧸ Ideal.ofList [x, y]` is flat over
`A`, but the images of `x`, `y` in `B ⧸ Ideal.map (algebraMap A B) (maximalIdeal A)` form
neither a regular sequence nor a Koszul-regular sequence. -/
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
