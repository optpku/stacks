/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.Coskeleton.Existence
public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.Coskeleton.Degreewise
public import ReasLib.CategoryTheory.Limits.FiniteConnected.Preserves
public import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Functors commuting with positive coskeletons

A functor preserving finite connected limits preserves the pointwise right Kan extensions along
a positive truncated-simplex inclusion.  This file packages the resulting objectwise and natural
comparison isomorphisms independently of any particular coefficient-category functor.
-/

@[expose] public section

open CategoryTheory.Limits Opposite

noncomputable section

universe u₁ v₁ u₂ v₂

namespace CategoryTheory.SimplicialObject.Truncated.coskeleton.comp

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

namespace matching

/-- A finite-connected-limit-preserving functor preserves limits of every positive-coskeleton
matching-index shape. -/
@[stacks 08NJ "preservation of positive coskeleton matching limits"]
instance preservesLimitsOfShape
    (G : C ⥤ D) {k n : ℕ} [NeZero k] [PreservesFiniteConnectedLimits G] :
    PreservesLimitsOfShape
      (coskeleton.degree.Index k (SimplexCategory.mk n)) G :=
  PreservesFiniteConnectedLimits.out
    (F := G) (coskeleton.degree.Index k (SimplexCategory.mk n))

end matching

/-- A finite-connected-limit-preserving functor preserves all pointwise right Kan extensions
along a positive truncated-simplex inclusion. -/
@[stacks 08NJ "finite-connected-limit functors preserve positive coskeletons"]
noncomputable instance preservesPointwise
    (G : C ⥤ D) (k : ℕ) [NeZero k] [PreservesFiniteConnectedLimits G] :
    G.PreservesPointwiseRightKanExtensions
      (SimplexCategory.Truncated.inclusion k).op :=
  fun F ⟨⟨n⟩⟩ ↦
    Functor.preservesPointwiseRightKanExtensionAtOfPreservesLimit
      (G := G) (F := F) (L := (SimplexCategory.Truncated.inclusion k).op)
        (op (SimplexCategory.mk n))

/-- The objectwise comparison between applying a functor after a chosen coskeleton and taking
the chosen coskeleton after applying the functor. -/
@[stacks 08NJ "objectwise functor-coskeleton comparison"]
noncomputable def isoApp
    (G : C ⥤ D) {k : ℕ} (U : SimplicialObject.Truncated C k)
    [U.HasCoskeleton]
    [G.PreservesRightKanExtension U (SimplexCategory.Truncated.inclusion k).op] :
    U.coskeleton ⋙ G ≅ SimplicialObject.Truncated.coskeleton (U ⋙ G) :=
  G.rightKanExtensionCompIsoOfPreserves U
    (SimplexCategory.Truncated.inclusion k).op

namespace isoApp

/-- The forward objectwise functor-coskeleton comparison is compatible with the chosen
right-Kan-extension counits. -/
@[reassoc (attr := simp), stacks 08NJ "functor-coskeleton comparison and counit"]
theorem hom_counit
    (G : C ⥤ D) {k : ℕ} (U : SimplicialObject.Truncated C k)
    [U.HasCoskeleton]
    [G.PreservesRightKanExtension U (SimplexCategory.Truncated.inclusion k).op]
    (a : (SimplexCategory.Truncated k)ᵒᵖ) :
    (isoApp G U).hom.app ((SimplexCategory.Truncated.inclusion k).op.obj a) ≫
        ((SimplexCategory.Truncated.inclusion k).op.rightKanExtensionCounit
          (U ⋙ G)).app a =
      G.map (((SimplexCategory.Truncated.inclusion k).op.rightKanExtensionCounit U).app a) := sorry

/-- The inverse objectwise functor-coskeleton comparison is compatible with the chosen
right-Kan-extension counits. -/
@[reassoc (attr := simp), stacks 08NJ "inverse functor-coskeleton comparison and counit"]
theorem inv_counit
    (G : C ⥤ D) {k : ℕ} (U : SimplicialObject.Truncated C k)
    [U.HasCoskeleton]
    [G.PreservesRightKanExtension U (SimplexCategory.Truncated.inclusion k).op]
    (a : (SimplexCategory.Truncated k)ᵒᵖ) :
    (isoApp G U).inv.app ((SimplexCategory.Truncated.inclusion k).op.obj a) ≫
        G.map (((SimplexCategory.Truncated.inclusion k).op.rightKanExtensionCounit U).app a) =
      ((SimplexCategory.Truncated.inclusion k).op.rightKanExtensionCounit
        (U ⋙ G)).app a := sorry

end isoApp

/-- A finite-connected-limit-preserving functor commutes naturally with positive coskeleton
functors whenever the source has pointwise coskeletons and the target has coskeletons. -/
@[stacks 08NJ "finite-connected-limit functor commutes with positive coskeleton"]
noncomputable def iso
    (G : C ⥤ D) (k : ℕ) [NeZero k] [PreservesFiniteConnectedLimits G]
    [SimplicialObject.Truncated.HasPointwiseCoskeletons C k]
    [SimplicialObject.Truncated.HasCoskeletons D k] :
    (Truncated.cosk k :
        SimplicialObject.Truncated C k ⥤ SimplicialObject C) ⋙
          (SimplicialObject.whiskering C D).obj G ≅
      (SimplicialObject.Truncated.whiskering C D).obj G ⋙
        (Truncated.cosk k :
          SimplicialObject.Truncated D k ⥤ SimplicialObject D) :=
  G.ranCompIsoOfPreserves (SimplexCategory.Truncated.inclusion k).op

/-- The component of the natural functor-coskeleton comparison is the objectwise comparison. -/
@[stacks 08NJ "natural and objectwise functor-coskeleton comparisons"]
theorem iso_app
    (G : C ⥤ D) (k : ℕ) [NeZero k] [PreservesFiniteConnectedLimits G]
    [SimplicialObject.Truncated.HasPointwiseCoskeletons C k]
    [SimplicialObject.Truncated.HasCoskeletons D k]
    (U : SimplicialObject.Truncated C k) :
    (iso G k).app U = isoApp G U := sorry

end CategoryTheory.SimplicialObject.Truncated.coskeleton.comp
