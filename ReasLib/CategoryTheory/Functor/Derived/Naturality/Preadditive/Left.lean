/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Preadditive.FunctorCategory
public import ReasLib.CategoryTheory.Functor.Derived.Naturality.Left

/-!
# Preadditive Naturality of Total Left-Derived Functors

Total left derivation preserves the additive structure on natural transformations whenever
the target category is preadditive. No additive structure is required on the source or
localized category, and the functors themselves need not be additive.
-/

@[expose] public section

noncomputable section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.Functor.LeftDerived

variable {C : Type u₁} {D : Type u₂} {E : Type u₃}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E] [Preadditive E]

/-- Total left-derived maps preserve zero natural transformations. -/
@[stacks 05T2, simp]
theorem mapNatTrans.zero
    (L : C ⥤ D) (S : MorphismProperty C) {F G : C ⥤ E}
    [L.IsLocalization S] [F.HasLeftDerivedFunctor S] [G.HasLeftDerivedFunctor S] :
    mapNatTrans L S (0 : F ⟶ G) = 0 := sorry

/-- Total left-derived maps preserve addition of source natural transformations. -/
@[stacks 05T2, simp]
theorem mapNatTrans.add
    (L : C ⥤ D) (S : MorphismProperty C) {F G : C ⥤ E}
    (τ σ : F ⟶ G) [L.IsLocalization S]
    [F.HasLeftDerivedFunctor S] [G.HasLeftDerivedFunctor S] :
    mapNatTrans L S (τ + σ) =
      mapNatTrans L S τ + mapNatTrans L S σ := sorry

end CategoryTheory.Functor.LeftDerived
