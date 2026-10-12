/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Preadditive.FunctorCategory
public import ReasLib.CategoryTheory.Functor.Derived.Naturality.Right

/-!
# Preadditive Naturality of Total Right-Derived Functors

Total right derivation preserves the additive structure on natural transformations whenever
the target category is preadditive. No additive structure is required on the source or
localized category, and the functors themselves need not be additive.
-/

@[expose] public section

noncomputable section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.Functor.RightDerived

variable {C : Type u₁} {D : Type u₂} {E : Type u₃}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E] [Preadditive E]

/-- Total right-derived maps preserve zero natural transformations. -/
@[stacks 05T2, simp]
theorem mapNatTrans.zero
    (L : C ⥤ D) (S : MorphismProperty C) {F G : C ⥤ E}
    [L.IsLocalization S] [F.HasRightDerivedFunctor S] [G.HasRightDerivedFunctor S] :
    mapNatTrans L S (0 : F ⟶ G) = 0 := sorry

/-- Total right-derived maps preserve addition of source natural transformations. -/
@[stacks 05T2, simp]
theorem mapNatTrans.add
    (L : C ⥤ D) (S : MorphismProperty C) {F G : C ⥤ E}
    (τ σ : F ⟶ G) [L.IsLocalization S]
    [F.HasRightDerivedFunctor S] [G.HasRightDerivedFunctor S] :
    mapNatTrans L S (τ + σ) =
      mapNatTrans L S τ + mapNatTrans L S σ := sorry

end CategoryTheory.Functor.RightDerived
