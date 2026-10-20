/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.IdealPower.Completion

/-!
# Derived completion over a Noetherian ring

@stack 0922
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u

variable {A : Type u} [CommRing A]

local notation "DMod" => DerivedCategory (ModuleCat A)

/- Proposition 15.95.2: over a Noetherian ring, the derived limit of the ideal-power quotient
tensor tower is the reflector from `D(A)` to the full subcategory of objects derived complete
with respect to the ideal. -/
section

variable [IsNoetherianRing A]

@[stacks 0922 "Proposition 15.95.2"]
#check fun (I : Ideal A)
    (L : DMod ⥤ (_root_.DerivedCategory.derivedCompleteObjectProperty I).FullSubcategory)
    (η : 𝟭 DMod ⟶
      L ⋙ (_root_.DerivedCategory.derivedCompleteObjectProperty I).ι)
    (hη : ∀ K : DMod,
      CategoryTheory.DerivedCategory.IdealPower.IsCompletionComparison
        I K (L.obj K).obj (η.app K)) ↦
  (CategoryTheory.DerivedCategory.IdealPower.completionFunctor_isLeftAdjoint I L η hη :
    L.IsLeftAdjoint)

end

/- The source comparison is carried by explicit maps to every quotient-tensor stage and a
derived-limit presentation of the target. -/
#check fun (I : Ideal A) (K : DMod) (n : ℕ) ↦
  (CategoryTheory.DerivedCategory.IdealPower.toStage I K n :
    K ⟶
      (CategoryTheory.DerivedCategory.IdealPower.tensorSystem I K).obj (op n))

#check fun (I : Ideal A) (K L : DMod) (c : K ⟶ L) ↦
  (CategoryTheory.DerivedCategory.IdealPower.IsCompletionComparison I K L c : Prop)

#check fun (I : Ideal A) (K L : DMod) (c : K ⟶ L) ↦
  (CategoryTheory.DerivedCategory.IdealPower.isCompletionComparison_iff I K L c :
    CategoryTheory.DerivedCategory.IdealPower.IsCompletionComparison I K L c ↔
      ∃ h :
          IsDerivedLimit
            (CategoryTheory.DerivedCategory.IdealPower.tensorSystem I K) L,
        ∀ n : ℕ, c ≫ h.stageProjection n =
          CategoryTheory.DerivedCategory.IdealPower.toStage I K n)

/- The Noetherian criterion identifies derived completeness with invertibility of the canonical
completion comparison. -/
section

variable [IsNoetherianRing A]

#check fun (I : Ideal A) (K L : DMod) (c : K ⟶ L)
    (hc : CategoryTheory.DerivedCategory.IdealPower.IsCompletionComparison I K L c) ↦
  (CategoryTheory.DerivedCategory.IdealPower.isDerivedComplete_iff_isIso I c hc :
    K.IsDerivedCompleteWithRespectTo I ↔ IsIso c)

end
