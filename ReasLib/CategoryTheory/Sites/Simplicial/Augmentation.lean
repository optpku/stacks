/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import ReasLib.CategoryTheory.Sites.ExactMorphismOfSites
public import ReasLib.CategoryTheory.Sites.Precoverage.Cocontinuous

/-!
# Augmentations of simplicial diagrams of sites

Augmentations are presenting functors whose composites along all zero-simplex
operators agree. Covariant diagrams use functors presenting exact morphisms of
sites in the reverse direction; contravariant diagrams use cocontinuous functors.
-/

@[expose] public section

universe u v w uD vD

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace CategoryTheory.SimplicialSites

section

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable {D : Type u} [Category.{v} D] (K : Precoverage D)
variable (u0 : D ⥤ C.obj ⦋0⦌)
variable [HasWeakSheafify (J ⦋0⦌).toGrothendieck (Type w)]
variable [∀ P : Dᵒᵖ ⥤ Type w, u0.op.HasLeftKanExtension P]

/-- An augmentation of a covariant diagram towards `(D, K)` is a functor `u0`
presenting a morphism of sites from `(C.obj ⦋0⦌, J ⦋0⦌)` to `(D, K)` whose
composites along all zero-simplex operators agree. -/
class IsAugmentation : Prop where
  /-- The functor `u0 : D ⥤ C.obj ⦋0⦌` presents an exact morphism of sites
  from `(C.obj ⦋0⦌, J ⦋0⦌)` to `(D, K)`. -/
  isExactMorphism :
    IsExactMorphismOfSites K.toGrothendieck (J ⦋0⦌).toGrothendieck u0
  /-- The composites `u_φ ∘ u0` agree for all `φ, ψ : ⦋0⦌ ⟶ n`. -/
  map_eq : ∀ {n : SimplexCategory} (φ ψ : ⦋0⦌ ⟶ n),
    u0 ⋙ (C.map φ).toFunctor = u0 ⋙ (C.map ψ).toFunctor

/-- A functor is an augmentation precisely when it presents an exact morphism
of sites and its composites along all zero-simplex operators agree. -/
theorem IsAugmentation.iff :
    IsAugmentation C J K u0 ↔
      IsExactMorphismOfSites K.toGrothendieck (J ⦋0⦌).toGrothendieck u0 ∧
        ∀ {n : SimplexCategory} (φ ψ : ⦋0⦌ ⟶ n),
          u0 ⋙ (C.map φ).toFunctor = u0 ⋙ (C.map ψ).toFunctor :=
  sorry

variable [h_aug : IsAugmentation C J K u0]
include h_aug

/-- An augmentation functor presents an exact morphism of sites in the reverse direction. -/
instance IsAugmentation.instIsExactMorphismOfSites :
    IsExactMorphismOfSites K.toGrothendieck (J ⦋0⦌).toGrothendieck u0 :=
  h_aug.isExactMorphism

/-- The sheaf inverse image along an augmentation functor preserves finite limits. -/
instance IsAugmentation.instSheafPullbackPreservesFiniteLimits :
    PreservesFiniteLimits
      (u0.sheafPullback (Type w) K.toGrothendieck (J ⦋0⦌).toGrothendieck) :=
  h_aug.isExactMorphism.preservesFiniteLimits_sheafPullback

/-- The two face operators `δ 0, δ 1 : ⦋0⦌ ⟶ ⦋1⦌` yield the same composite with `u0`. -/
theorem IsAugmentation.face_eq :
    u0 ⋙ (C.map (SimplexCategory.δ 0 : ⦋0⦌ ⟶ ⦋1⦌)).toFunctor =
      u0 ⋙ (C.map (SimplexCategory.δ 1 : ⦋0⦌ ⟶ ⦋1⦌)).toFunctor :=
  sorry

/-- The composite `u_n = u_φ ∘ u0` along the constant operator `⦋0⦌ ⟶ n`. -/
def IsAugmentation.stageFunctor (n : SimplexCategory) : D ⥤ C.obj n :=
  u0 ⋙ (C.map (SimplexCategory.const ⦋0⦌ n 0)).toFunctor

/-- Every composite `u_φ ∘ u0` equals the stage functor at `n`. -/
theorem IsAugmentation.stageFunctor_eq {n : SimplexCategory} (φ : ⦋0⦌ ⟶ n) :
    u0 ⋙ (C.map φ).toFunctor = IsAugmentation.stageFunctor C u0 n :=
  sorry

end

/-- The identity on a site is an augmentation of the constant simplex diagram. -/
instance IsAugmentation.const {D : Type u} [Category.{v} D] (K : Precoverage D)
    [HasWeakSheafify K.toGrothendieck (Type w)]
    [∀ P : Dᵒᵖ ⥤ Type w, (𝟭 D).op.HasLeftKanExtension P] :
    IsAugmentation ((Functor.const SimplexCategory).obj (Cat.of D)) (fun _ ↦ K) K (𝟭 D) :=
  sorry

end CategoryTheory.SimplicialSites

namespace CategoryTheory.Grothendieck

section

variable (F : SimplicialObject Cat.{v, u}) (J : ∀ n, Precoverage (F.obj n))
variable {D : Type uD} [Category.{vD} D] (K : Precoverage D)
variable (u0 : F.obj (op ⦋0⦌) ⥤ D)

/-- An augmentation of a contravariant diagram towards `(D, K)` is a
cocontinuous functor `u0` whose composites after precomposition by all
zero-simplex operators agree. -/
class IsAugmentation : Prop where
  /-- `u0` is cocontinuous for the chosen stage and target precoverages. -/
  isCocontinuous : Functor.Precoverage.IsCocontinuous u0 (J (op ⦋0⦌)) K
  /-- The composites `u0 ∘ u_φ` agree for all `φ, ψ : ⦋0⦌ ⟶ n`. -/
  map_eq : ∀ {n : SimplexCategory} (φ ψ : ⦋0⦌ ⟶ n),
    (F.map φ.op).toFunctor ⋙ u0 = (F.map ψ.op).toFunctor ⋙ u0

/-- A functor is an augmentation precisely when it is cocontinuous and its
composites after precomposition by all zero-simplex operators agree. -/
theorem IsAugmentation.iff :
    IsAugmentation F J K u0 ↔
      Functor.Precoverage.IsCocontinuous u0 (J (op ⦋0⦌)) K ∧
        ∀ {n : SimplexCategory} (φ ψ : ⦋0⦌ ⟶ n),
          (F.map φ.op).toFunctor ⋙ u0 = (F.map ψ.op).toFunctor ⋙ u0 :=
  sorry

variable [h_aug : IsAugmentation F J K u0]
include h_aug

/-- An augmentation functor is cocontinuous for the chosen precoverages. -/
instance IsAugmentation.instIsCocontinuous :
    Functor.Precoverage.IsCocontinuous u0 (J (op ⦋0⦌)) K :=
  h_aug.isCocontinuous

/-- The two face operators `δ 0, δ 1 : ⦋0⦌ ⟶ ⦋1⦌` yield the same composite with `u0`. -/
theorem IsAugmentation.face_eq :
    (F.map (SimplexCategory.δ 0 : ⦋0⦌ ⟶ ⦋1⦌).op).toFunctor ⋙ u0 =
      (F.map (SimplexCategory.δ 1 : ⦋0⦌ ⟶ ⦋1⦌).op).toFunctor ⋙ u0 :=
  sorry

/-- The composite `u_n = u0 ∘ u_φ` along the constant operator `⦋0⦌ ⟶ n`. -/
def IsAugmentation.stageFunctor (n : SimplexCategory) : F.obj (op n) ⥤ D :=
  (F.map (SimplexCategory.const ⦋0⦌ n 0).op).toFunctor ⋙ u0

/-- Every composite `u0 ∘ u_φ` equals the stage functor at `n`. -/
theorem IsAugmentation.stageFunctor_eq {n : SimplexCategory} (φ : ⦋0⦌ ⟶ n) :
    (F.map φ.op).toFunctor ⋙ u0 = IsAugmentation.stageFunctor F u0 n :=
  sorry

end

/-- The identity on a site is an augmentation of the constant simplicial diagram. -/
instance IsAugmentation.const {D : Type uD} [Category.{vD} D] (K : Precoverage D) :
    IsAugmentation ((Functor.const SimplexCategoryᵒᵖ).obj (Cat.of D)) (fun _ ↦ K) K (𝟭 D) :=
  sorry

end CategoryTheory.Grothendieck
