/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Extension.Cotangent.NaiveComplex.Smooth
import StacksCheckRecall

/-!
# Smoothness and the naive cotangent complex

Remark 15.85.2 records the smooth and formally smooth criteria given by degree-one Ext
vanishing for `NL{B/A}`.

@stack 0G9D
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open scoped DerivedExt

universe u v

/- Remark 15.85.2 (1) (0G9D), the smoothness criterion. -/
@[stacks 0G9D "Remark 15.85.2 (1)"]
#check fun (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B] =>
  (Algebra.smooth_iff_finitePresentation_and_naiveCotangent_extOne_vanishes A B :
    Algebra.Smooth A B ↔ Algebra.FinitePresentation A B ∧
      ∀ (N : ModuleCat B), ∀ e : Ext⁽(1 : ℤ)⁾(Algebra.naiveCotangentObject A B,
          (DerivedCategory.singleFunctor (ModuleCat B) (0 : ℤ)).obj N), e = 0)

/- Remark 15.85.2 (2) (0G9D), the formal-smoothness criterion. -/
@[stacks 0G9D "Remark 15.85.2 (2)"]
#check fun (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B] =>
  (Algebra.formallySmooth_iff_naiveCotangent_extOne_vanishes A B :
    Algebra.FormallySmooth A B ↔
      ∀ (N : ModuleCat B), ∀ e : Ext⁽(1 : ℤ)⁾(Algebra.naiveCotangentObject A B,
          (DerivedCategory.singleFunctor (ModuleCat B) (0 : ℤ)).obj N), e = 0)

@[stacks 0G9D "smoothness zero-functor companion"]
#check fun (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B] =>
  (Algebra.smooth_iff_finitePresentation_and_naiveCotangent_extOneFunctor_isZero A B :
    Algebra.Smooth A B ↔ Algebra.FinitePresentation A B ∧
      IsZero (CategoryTheory.DerivedCategory.Ext.addCommGrpFunctor
        (Algebra.naiveCotangentObject A B) (1 : ℤ)))

@[stacks 0G9D "formal-smoothness zero-functor companion"]
#check fun (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B] =>
  (Algebra.formallySmooth_iff_naiveCotangent_extOneFunctor_isZero A B :
    Algebra.FormallySmooth A B ↔
      IsZero (CategoryTheory.DerivedCategory.Ext.addCommGrpFunctor
        (Algebra.naiveCotangentObject A B) (1 : ℤ)))
