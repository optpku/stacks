module

public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import ReasLib.Algebra.Category.CommRingCat.Under.ModulePair

/-!
# Trivial square-zero extensions as objects of `S`-Alg/`R`

The assignment `M ↦ R[M]` is the functor `ModuleCat R ⥤ Over (CommAlgCat.of S R)`
sending an `R`-module to the trivial square-zero extension `TrivSqZeroExt R M`,
viewed as an `S`-algebra over `R` via the canonical projection.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace TrivSqZeroExt

variable (S : Type u) [CommRing S]

/-- Typecheck an `S`-algebra homomorphism as a morphism in `CommAlgCat S`. -/
def homOfAlgHom {X Y : Type u} [CommRing X] [Algebra S X] [CommRing Y] [Algebra S Y]
    (f : X →ₐ[S] Y) : CommAlgCat.of S X ⟶ CommAlgCat.of S Y :=
  CommAlgCat.ofHom f

/-- `homOfAlgHom` is the `CommAlgCat` packaging of an `S`-algebra homomorphism. -/
theorem homOfAlgHom_apply {X Y : Type u} [CommRing X] [Algebra S X] [CommRing Y] [Algebra S Y]
    (f : X →ₐ[S] Y) : homOfAlgHom S f = CommAlgCat.ofHom f := sorry

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

/-- Finite products in `S`-Alg/`R` are fiber products over `R`. -/
instance instHasFiniteProducts_over :
    HasFiniteProducts (Over (CommAlgCat.of S R)) :=
  Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks

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
    homOfAlgHom S (overFunctor_mapAlgHom S R f) ≫ homOfAlgHom S (fstHom S R N) =
      homOfAlgHom S (fstHom S R M) := sorry

/-- The functor `Mod_R ⥤ S`-Alg/`R` sending `M` to the trivial square-zero extension
`R[M]`, as an `S`-algebra over `R`. -/
def overFunctor : ModuleCat.{u} R ⥤ Over (CommAlgCat.of S R) where
  obj M := Over.mk (homOfAlgHom S (fstHom S R M))
  map f := Over.homMk (homOfAlgHom S (overFunctor_mapAlgHom S R f)) (overFunctor_map_w S R f)
  map_id := sorry
  map_comp := sorry

/-- Objects of `overFunctor` are trivial square-zero extensions over `R`. -/
theorem overFunctor_obj (M : ModuleCat.{u} R) :
    (overFunctor S R).obj M = Over.mk (homOfAlgHom S (fstHom S R M)) := sorry

/-- Morphisms of `overFunctor` are the induced `S`-algebra maps of square-zero
extensions, as morphisms over `R`. -/
theorem overFunctor_map {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    (overFunctor S R).map f =
      Over.homMk (homOfAlgHom S (overFunctor_mapAlgHom S R f)) (overFunctor_map_w S R f) :=
  sorry

end TrivSqZeroExt
