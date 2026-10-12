/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
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
instance instIsCentralScalar (M : ModuleCat.{u} R) : IsCentralScalar R M :=
  ModulePair.instIsCentralScalar (CommRingCat.of R) M

/-- The trivial square-zero extension of a bundled `R`-module is a commutative ring. -/
instance instCommRing (M : ModuleCat.{u} R) : CommRing (TrivSqZeroExt R M) :=
  inferInstance

variable [Algebra S R]

/-- Restriction of scalars along `S → R` on a bundled `R`-module. -/
instance instModuleRestrictScalars (M : ModuleCat.{u} R) : Module S M :=
  Module.compHom M (algebraMap S R)

/-- Restriction of scalars along `S → R` is a scalar tower on a bundled `R`-module. -/
instance instIsScalarTower_restrictScalars (M : ModuleCat.{u} R) :
    IsScalarTower S R M := sorry

/-- Restriction of scalars is a scalar tower with respect to the opposite `R`-action. -/
instance instIsScalarTower_op (M : ModuleCat.{u} R) : IsScalarTower S Rᵐᵒᵖ M := sorry

/-- The induced `S`-algebra map `R[M] →ₐ[S] R[N]` of a linear map `M ⟶ N`. -/
def overFunctor_mapAlgHom {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    TrivSqZeroExt R M →ₐ[S] TrivSqZeroExt R N where
  toRingHom := (map f.hom).toRingHom
  commutes' := sorry

/-- The induced square-zero algebra map acts as `TrivSqZeroExt.map` on the underlying rings. -/
theorem overFunctor_mapAlgHom_toRingHom {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    (overFunctor_mapAlgHom S R f).toRingHom = (map f.hom).toRingHom := sorry

/-- The structure map of `R[N]` after an induced square-zero algebra map equals the
structure map of `R[M]`. -/
theorem overFunctor_map_w {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    CommAlgCat.ofHom (overFunctor_mapAlgHom S R f) ≫ CommAlgCat.ofHom (fstHom S R N) =
      CommAlgCat.ofHom (fstHom S R M) := sorry

/-- The functor `Mod_R ⥤ S`-Alg/`R` sending `M` to the trivial square-zero extension
`R[M]`, as an `S`-algebra over `R`. -/
def overFunctor : ModuleCat.{u} R ⥤ Over (CommAlgCat.of S R) where
  obj M := Over.mk (CommAlgCat.ofHom (fstHom S R M))
  map f := Over.homMk (CommAlgCat.ofHom (overFunctor_mapAlgHom S R f)) (overFunctor_map_w S R f)
  map_id := sorry
  map_comp := sorry

/-- Objects of `overFunctor` are trivial square-zero extensions over `R`. -/
theorem overFunctor_obj (M : ModuleCat.{u} R) :
    (overFunctor S R).obj M = Over.mk (CommAlgCat.ofHom (fstHom S R M)) := sorry

/-- Morphisms of `overFunctor` are the induced `S`-algebra maps of square-zero
extensions, as morphisms over `R`. -/
theorem overFunctor_map {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    (overFunctor S R).map f =
      Over.homMk (CommAlgCat.ofHom (overFunctor_mapAlgHom S R f)) (overFunctor_map_w S R f) :=
  sorry

end TrivSqZeroExt
