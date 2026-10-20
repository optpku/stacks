/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.Normalized.Ext

@[expose] public section

open CategoryTheory
open scoped DerivedExt

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory.IsNormalizedDualizingComplex

/- Remark 47.16.6: a normalized dualizing complex over a Noetherian local ring of
Krull dimension `d` has injective amplitude in `[-d, 0]`. -/
@[stacks 0BUJ] #check
  (CategoryTheory.DerivedCategory.IsNormalizedDualizingComplex.hasInjectiveAmplitudeIn :
    ∀ (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (ω : DerivedCategory (ModuleCat.{u} A)), ω.IsNormalizedDualizingComplex H →
    ∀ (d : ℕ), ringKrullDim A = d → ω.HasInjectiveAmplitudeIn (-(d : ℤ)) 0)

/- Consequently, derived Ext from every module vanishes outside that interval. -/
#check
  (CategoryTheory.DerivedCategory.IsNormalizedDualizingComplex.ext_subsingleton :
    ∀ (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (ω : DerivedCategory (ModuleCat.{u} A)), ω.IsNormalizedDualizingComplex H →
    ∀ (d : ℕ), ringKrullDim A = d → ∀ (M : ModuleCat.{u} A) (i : ℤ),
    i ∉ Set.Icc (-(d : ℤ)) 0 → Subsingleton (Ext⁽i⁾(ModuleCat.single0 M, ω)))

end CategoryTheory.DerivedCategory.IsNormalizedDualizingComplex
