/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Limits

@[expose] public section
open CategoryTheory CategoryTheory.Limits
universe u v w v₁ w₁
namespace ModuleCat.ReindexedLimit

variable {R S : Type u} [CommRing R] [CommRing S]
variable (f : R →+* S)
variable {J : Type v} [Category.{w} J] {K : Type v₁} [Category.{w₁} K]
variable [Small.{u} J] [Small.{u} K]
variable (F : J ⥤ ModuleCat.{u} R) (G : K ⥤ ModuleCat.{u} S)
variable (k : K ⥤ J)
variable (α : k ⋙ F ⟶ G ⋙ ModuleCat.restrictScalars f)

/-- Reindex the source inverse limit, apply the specified stage maps,
then use the canonical fact that scalar restriction preserves limits. -/
noncomputable def underlyingMap :
    limit F ⟶ (ModuleCat.restrictScalars f).obj (limit G) :=
  limit.pre F k ≫ limMap α ≫ (preservesLimitIso (ModuleCat.restrictScalars f) G).inv

/-- Each projection of the limit map is the supplied component map after
the corresponding reindexed source projection. -/
theorem underlyingMap_projection (e : K) :
    underlyingMap f F G k α ≫ (ModuleCat.restrictScalars f).map (limit.π G e) =
      limit.π F (k.obj e) ≫ α.app e := by
  simp only [underlyingMap, Category.assoc, preservesLimitIso_inv_π]
  erw [limMap_π, ← Category.assoc, limit.pre_π]
  rfl

/-- The actual reindexed limit comparison, exposed as an f-semilinear
map. No inverse or comparison of unrelated module carriers is chosen. -/
noncomputable def map : (limit F : ModuleCat.{u} R) →ₛₗ[f] (limit G : ModuleCat.{u} S) where
  toFun := (underlyingMap f F G k α).hom
  map_add' := (underlyingMap f F G k α).hom.map_add
  map_smul' := (underlyingMap f F G k α).hom.map_smul

/-- Evaluation at a target stage computes precisely the specified map
from its reindexed source stage. -/
theorem map_projection (e : K) (x : (limit F : ModuleCat.{u} R)) :
    limit.π G e (map f F G k α x) = α.app e (limit.π F (k.obj e) x) :=
  ConcreteCategory.congr_hom (underlyingMap_projection f F G k α e) x

end ModuleCat.ReindexedLimit
