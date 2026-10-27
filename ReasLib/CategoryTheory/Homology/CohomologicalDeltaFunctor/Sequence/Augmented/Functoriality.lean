/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Homology.CohomologicalDeltaFunctor.Sequence.Augmented.Naturality
public import ReasLib.CategoryTheory.Homology.CohomologicalDeltaFunctor.Sequence.Functoriality
public import ReasLib.CategoryTheory.ComposableArrows.ZeroPrecomp.Functor
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Functorial Augmented Cohomological Windows

Augmented low-degree windows form a functor on short exact complexes and
vary functorially with the cohomological delta functor.
-/

open CategoryTheory.ComposableArrows
open CategoryTheory.Limits

noncomputable section

universe vA uA vB uB

namespace CategoryTheory.CohomologicalDeltaFunctor.augmentedWindow

variable {A : Type uA} [Category.{vA} A] [Preadditive A]
variable {B : Type uB} [Category.{vB} B] [Preadditive B]

/-- Augmented low-degree windows of a fixed cohomological delta functor are
functorial in the short exact complex. -/
@[stacks 010R "functor of augmented cohomological windows"]
noncomputable def functor (F : CohomologicalDeltaFunctor A B)
    [HasZeroObject B] :
    (ShortComplex.shortExact A).FullSubcategory ⥤ ComposableArrows B 6 :=
  exactWindow.functor F 0 ⋙ zeroPrecomp.functor 1

variable [HasZeroObject B]

/-- The object action of the augmented-window functor is the pointwise
augmented window. -/
@[simp]
theorem functor_obj (F : CohomologicalDeltaFunctor A B)
    (S : (ShortComplex.shortExact A).FullSubcategory) :
    (functor F).obj S = F.augmentedWindow S.property := rfl

/-- The morphism action of the augmented-window functor is the pointwise
naturality map. -/
@[simp]
theorem functor_map (F : CohomologicalDeltaFunctor A B)
    {S T : (ShortComplex.shortExact A).FullSubcategory} (φ : S ⟶ T) :
    (functor F).map φ = map F S.property T.property φ.hom := rfl

/-- Pointwise augmented model maps are natural in the short exact complex. -/
theorem natTrans_naturality {F G : CohomologicalDeltaFunctor A B}
    (τ : F ⟶ G) {S T : (ShortComplex.shortExact A).FullSubcategory}
    (φ : S ⟶ T) :
    (functor F).map φ ≫ modelMap τ T.property =
      modelMap τ S.property ≫ (functor G).map φ := by
  apply NatTrans.ext
  funext i
  fin_cases i
  · rfl
  · exact (τ.app 0).naturality φ.hom.τ₁
  · exact (τ.app 0).naturality φ.hom.τ₂
  · exact (τ.app 0).naturality φ.hom.τ₃
  · exact (τ.app 1).naturality φ.hom.τ₁
  · exact (τ.app 1).naturality φ.hom.τ₂
  · exact (τ.app 1).naturality φ.hom.τ₃

/-- A morphism of cohomological delta functors induces a natural
transformation between their augmented-window functors. -/
@[stacks 010R "natural transformation of augmented cohomological windows"]
noncomputable def natTrans {F G : CohomologicalDeltaFunctor A B} (τ : F ⟶ G) :
    functor F ⟶ functor G :=
  Functor.whiskerRight (exactWindow.natTrans τ 0) (zeroPrecomp.functor 1)

/-- The component of an augmented-window natural transformation is the
pointwise augmented model map. -/
@[simp]
theorem natTrans_app {F G : CohomologicalDeltaFunctor A B} (τ : F ⟶ G)
    (S : (ShortComplex.shortExact A).FullSubcategory) :
    (natTrans τ).app S = modelMap τ S.property := rfl

/-- The identity delta-functor morphism induces the identity augmented-window
natural transformation. -/
@[simp]
theorem natTrans_id (F : CohomologicalDeltaFunctor A B) :
    natTrans (𝟙 F) = 𝟙 (functor F) := by
  apply NatTrans.ext
  funext S
  apply NatTrans.ext
  funext i
  fin_cases i <;> rfl

/-- Augmented-window natural transformations preserve composition. -/
@[simp]
theorem natTrans_comp {F G H : CohomologicalDeltaFunctor A B}
    (τ : F ⟶ G) (σ : G ⟶ H) :
    natTrans (τ ≫ σ) = natTrans τ ≫ natTrans σ := by
  apply NatTrans.ext
  funext S
  apply hom_ext_succ
  · exact (Category.id_comp _).symm
  · apply hom_ext₅ <;> rfl

/-- Taking the augmented low-degree window is functorial in the
cohomological delta functor. -/
@[stacks 010R "model functor of augmented cohomological windows"]
noncomputable def modelFunctor :
    CohomologicalDeltaFunctor A B ⥤
      ((ShortComplex.shortExact A).FullSubcategory ⥤ ComposableArrows B 6) :=
  exactWindow.modelFunctor 0 ⋙
    (Functor.whiskeringRight
      (ShortComplex.shortExact A).FullSubcategory
      (ComposableArrows B 5) (ComposableArrows B 6)).obj
        (zeroPrecomp.functor 1)

/-- Forgetting the initial zero component of the augmented-window functor
recovers the low-degree exact-window functor. -/
@[simp]
theorem functor_comp_δ₀ (F : CohomologicalDeltaFunctor A B) :
    functor F ⋙ δ₀Functor = exactWindow.functor F 0 := rfl

/-- Evaluating the augmented model functor at a delta functor gives its
augmented-window functor. -/
@[simp]
theorem modelFunctor_obj (F : CohomologicalDeltaFunctor A B) :
    (modelFunctor (A := A) (B := B)).obj F = functor F := rfl

/-- Evaluating an augmented model-functor map gives the pointwise augmented
model map. -/
@[simp]
theorem modelFunctor_map_app {F G : CohomologicalDeltaFunctor A B}
    (τ : F ⟶ G) (S : (ShortComplex.shortExact A).FullSubcategory) :
    ((modelFunctor (A := A) (B := B)).map τ).app S =
      modelMap τ S.property := rfl

end CategoryTheory.CohomologicalDeltaFunctor.augmentedWindow
