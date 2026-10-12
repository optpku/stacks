/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Birational.Counterexamples
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Example 29.50.4: over an infinite field, the morphism from the affine line to the affine
thickening defined by `(x - α)y_α` and `y_αy_β` is birational. -/
@[stacks 01RQ] #check
  (AlgebraicGeometry.BirationalCounterexample.AffineLineThickening.instIsBirationalToThickening :
    ∀ (k : Type u) [Field k] [Infinite k],
      AlgebraicGeometry.IsBirational
        (AlgebraicGeometry.BirationalCounterexample.AffineLineThickening.toThickening k))

#check
  (AlgebraicGeometry.BirationalCounterexample.AffineLineThickening.retraction_leftInverse :
    ∀ (k : Type u) [Field k],
      Function.LeftInverse
        (AlgebraicGeometry.BirationalCounterexample.AffineLineThickening.retraction k)
        (AlgebraicGeometry.BirationalCounterexample.AffineLineThickening.inclusion k))

#check
  (AlgebraicGeometry.BirationalCounterexample.AffineLineThickening.inclusion_injective :
    ∀ (k : Type u) [Field k],
      Function.Injective
        (AlgebraicGeometry.BirationalCounterexample.AffineLineThickening.inclusion k))

#check
  (AlgebraicGeometry.BirationalCounterexample.AffineLineThickening.instIsBirationalToBase :
    ∀ (k : Type u) [Field k] [Infinite k],
      AlgebraicGeometry.IsBirational
        (AlgebraicGeometry.BirationalCounterexample.AffineLineThickening.toBase k))

#check
  (AlgebraicGeometry.BirationalCounterexample.AffineLineThickening.not_isIso_restrict_toBase :
    ∀ (k : Type u) [Field k] [Infinite k]
      (U : (AlgebraicGeometry.BirationalCounterexample.AffineLineThickening.BaseScheme k).Opens),
      Nonempty U →
        ¬ IsIso
          (AlgebraicGeometry.BirationalCounterexample.AffineLineThickening.toBase k ∣_ U))

#check
  (AlgebraicGeometry.BirationalCounterexample.AffineLineThickening.not_isIso_restrict_toThickening :
    ∀ (k : Type u) [Field k] [Infinite k]
      (U :
        (AlgebraicGeometry.BirationalCounterexample.AffineLineThickening.ThickeningScheme k).Opens),
      Nonempty U →
        ¬ IsIso
          (AlgebraicGeometry.BirationalCounterexample.AffineLineThickening.toThickening k ∣_ U))

#check
  (AlgebraicGeometry.LocalizationMorphism.isBirational :
    ∀ (A : Type u) [CommRing A] [IsDomain A] (S : Submonoid A),
      (0 : A) ∉ S →
        AlgebraicGeometry.IsBirational (AlgebraicGeometry.LocalizationMorphism.hom A S))

#check
  (AlgebraicGeometry.LocalizationMorphism.exists_away_isUnit_of_exists_isIso_restrict :
    ∀ (A : Type u) [CommRing A] [IsDomain A] (S : Submonoid A),
      (0 : A) ∉ S →
        (∃ U : (AlgebraicGeometry.Spec (CommRingCat.of A)).Opens,
          Nonempty U ∧
            IsIso (AlgebraicGeometry.LocalizationMorphism.hom A S ∣_ U)) →
          ∃ a : A, ∀ s : S,
            IsUnit (algebraMap A (Localization.Away a) s.1))

#check
  (AlgebraicGeometry.BirationalCounterexample.OddLocalization.zero_not_mem :
    (0 : ℤ) ∉ AlgebraicGeometry.BirationalCounterexample.OddLocalization.submonoid)

#check
  (AlgebraicGeometry.BirationalCounterexample.OddLocalization.not_isIso_restrict :
    ∀ U : (AlgebraicGeometry.Spec (CommRingCat.of ℤ)).Opens,
      Nonempty U →
        ¬ IsIso
          (AlgebraicGeometry.LocalizationMorphism.hom ℤ
            AlgebraicGeometry.BirationalCounterexample.OddLocalization.submonoid ∣_ U))
