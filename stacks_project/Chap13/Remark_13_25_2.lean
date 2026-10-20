/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.Algebra.Homology.HomotopyCategory.Injective.Localization
import Mathlib.Algebra.Homology.DerivedCategory.Plus
import StacksCheckRecall

@[expose] public section

open CategoryTheory

/-!
# Remark 13.25.2

For the specified resolution functor and its lift j′ from Lemma 13.25.1,
applying an additive functor gives an exact functor D⁺(A) ⥤ K⁺(B).
Composing with K⁺(B) ⥤ D⁺(B) computes the right derived functor.
The lift is supplied as data; no resolution or shift comparison is selected
from a Prop-valued existence assertion.
-/

universe wA wB vA vB uA uB
variable {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B]
variable [Abelian A] [Abelian B] [EnoughInjectives A]
variable [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
variable (J : HomotopyCategory.Plus.InjectiveResolutionFunctor A)
variable (j' : DerivedCategory.Plus A ⥤ HomotopyCategory.Plus.Injective A)
variable (hj' : Localization.Lifting DerivedCategory.Plus.Qh
  (HomotopyCategory.Plus.quasiIso A) J.toFunctor j')
variable (F : A ⥤ B) [F.Additive]

/- The actual homotopy-valued factorization, with both endpoints explicit. -/
#check (j' ⋙ HomotopyCategory.Plus.Injective.ι A ⋙ F.mapHomotopyCategoryPlus :
  DerivedCategory.Plus A ⥤ HomotopyCategory.Plus B)

/- Remark 13.25.2 (0158): exactness of this same specified composite. -/
@[stacks 0158 "exact homotopy-valued lift of the right derived functor"] #check
  (J.lift_comp_mapHomotopyCategoryPlus_exact DerivedCategory.Plus.Qh j' hj' F :
    Functor.HasTriangulatedStructure
      (j' ⋙ HomotopyCategory.Plus.Injective.ι A ⋙ F.mapHomotopyCategoryPlus))

/- Its composition with the canonical target localization computes RF, with the
comparison coming from the supplied resolution and lifting isomorphism. -/
#check
  (J.lift_comp_isRightDerivedFunctor DerivedCategory.Plus.Qh j' hj'
      (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh) :
    (j' ⋙ HomotopyCategory.Plus.Injective.ι A ⋙
      (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh)).IsRightDerivedFunctor
        (J.liftComparison DerivedCategory.Plus.Qh j' hj'
          (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh))
        (HomotopyCategory.Plus.quasiIso A))
