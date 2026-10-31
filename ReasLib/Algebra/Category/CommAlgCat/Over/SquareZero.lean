/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import ReasLib.Algebra.Category.CommRingCat.Under.ModulePair

/-!
# Square-zero extensions over a commutative algebra

An `R`-module `M` determines the square-zero extension `R[M]` in
`Over (CommAlgCat.of S R)`, functorially in `M`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace TrivSqZeroExt

variable (S : Type u) [CommRing S]
variable (R : Type u) [CommRing R]

/-- The opposite `R`-action on a bundled `R`-module, using commutativity of `R`. -/
instance instModuleMulOpposite (M : ModuleCat.{u} R) : Module Rᵐᵒᵖ M :=
  ModulePair.instModuleMulOpposite (CommRingCat.of R) M

/-- Left and opposite `R`-actions on a bundled `R`-module agree. -/
instance instIsCentralScalar (M : ModuleCat.{u} R) : IsCentralScalar R M where
  op_smul_eq_smul _ _ := rfl

/-- The trivial square-zero extension of a bundled `R`-module is a commutative ring. -/
instance instCommRing (M : ModuleCat.{u} R) : CommRing (TrivSqZeroExt R M) :=
  inferInstance

variable [Algebra S R]

/-- Restriction of scalars along `S → R` on a bundled `R`-module. -/
instance instModuleRestrictScalars (M : ModuleCat.{u} R) : Module S M :=
  Module.compHom M (algebraMap S R)

/-- Restriction of scalars along `S → R` is a scalar tower on a bundled `R`-module. -/
instance instIsScalarTower_restrictScalars (M : ModuleCat.{u} R) :
    IsScalarTower S R M where
  smul_assoc _ _ _ := by
    rw [Algebra.smul_def, mul_smul]
    rfl

/-- Restriction of scalars is a scalar tower with respect to the opposite `R`-action. -/
instance instIsScalarTower_op (M : ModuleCat.{u} R) : IsScalarTower S Rᵐᵒᵖ M where
  smul_assoc s r m := by
    change (s • MulOpposite.unop r) • m = s • (MulOpposite.unop r • m)
    exact smul_assoc s (MulOpposite.unop r) m

/-- The induced `S`-algebra map `R[M] →ₐ[S] R[N]` of a linear map `M ⟶ N`. -/
def overFunctor_mapAlgHom {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    TrivSqZeroExt R M →ₐ[S] TrivSqZeroExt R N where
  toRingHom := (map f.hom).toRingHom
  commutes' s := by
    change map f.hom (algebraMap S (TrivSqZeroExt R M) s) =
      algebraMap S (TrivSqZeroExt R N) s
    rw [algebraMap_eq_inl', algebraMap_eq_inl', map_inl]

/-- The induced square-zero algebra map acts as `TrivSqZeroExt.map` on the underlying rings. -/
theorem overFunctor_mapAlgHom_toRingHom {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    (overFunctor_mapAlgHom S R f).toRingHom = (map f.hom).toRingHom := rfl

/-- The structure map of `R[N]` after an induced square-zero algebra map equals the
structure map of `R[M]`. -/
theorem overFunctor_map_w {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    CommAlgCat.ofHom (overFunctor_mapAlgHom S R f) ≫ CommAlgCat.ofHom (fstHom S R N) =
      CommAlgCat.ofHom (fstHom S R M) := by
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro x
  change fst (map f.hom x) = fst x
  exact fst_map f.hom x

/-- The functor `Mod_R ⥤ S`-Alg/`R` sending `M` to the trivial square-zero extension
`R[M]`, as an `S`-algebra over `R`. -/
def overFunctor : ModuleCat.{u} R ⥤ Over (CommAlgCat.of S R) where
  obj M := Over.mk (CommAlgCat.ofHom (fstHom S R M))
  map f := Over.homMk (CommAlgCat.ofHom (overFunctor_mapAlgHom S R f)) (overFunctor_map_w S R f)
  map_id M := by
    apply Over.OverMorphism.ext
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro x
    change map (LinearMap.id : M →ₗ[R] M) x = x
    rw [map_id]
    rfl
  map_comp f g := by
    apply Over.OverMorphism.ext
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro x
    change map (g.hom.comp f.hom) x = map g.hom (map f.hom x)
    exact DFunLike.congr_fun (map_comp_map f.hom g.hom) x

/-- Objects of `overFunctor` are trivial square-zero extensions over `R`. -/
theorem overFunctor_obj (M : ModuleCat.{u} R) :
    (overFunctor S R).obj M = Over.mk (CommAlgCat.ofHom (fstHom S R M)) := rfl

/-- Morphisms of `overFunctor` are the induced `S`-algebra maps of square-zero
extensions, as morphisms over `R`. -/
theorem overFunctor_map {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    (overFunctor S R).map f =
      Over.homMk (CommAlgCat.ofHom (overFunctor_mapAlgHom S R f)) (overFunctor_map_w S R f) :=
  rfl

end TrivSqZeroExt
