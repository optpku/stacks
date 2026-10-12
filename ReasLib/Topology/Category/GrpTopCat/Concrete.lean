/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Monoidal.Internal.Types.Grp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.GrpLimits
public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Topology.Category.TopCat.Monoidal

/-!
# Concrete topological groups

`Grp TopCat` is Mathlib's canonical category of internal group objects in topological spaces.
This module supplies its concrete realization by continuous group homomorphisms and the resulting
forgetful functor to `GrpCat`.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Monoidal MonoidalCategory CartesianMonoidalCategory MonObj

namespace GrpTopCat

/-- The carrier of a group object in `TopCat` has its induced ordinary group structure. -/
@[stacks 0B1Z "ordinary group underlying a topological group object"]
instance instGroup (X : Grp TopCat.{u}) : Group X.X where
  one := (TopCat.Hom.hom η[X.X]) PUnit.unit
  mul x y := (TopCat.Hom.hom μ[X.X]) (x, y)
  inv x := (TopCat.Hom.hom ι[X.X]) x
  one_mul x := by
    change (ConcreteCategory.hom (η[X.X] ▷ X.X ≫ μ[X.X])) (PUnit.unit, x) =
      (ConcreteCategory.hom (λ_ X.X).hom) (PUnit.unit, x)
    exact ConcreteCategory.congr_hom (MonObj.one_mul X.X) (PUnit.unit, x)
  mul_one x := by
    change (ConcreteCategory.hom (X.X ◁ η[X.X] ≫ μ[X.X])) (x, PUnit.unit) =
      (ConcreteCategory.hom (ρ_ X.X).hom) (x, PUnit.unit)
    exact ConcreteCategory.congr_hom (MonObj.mul_one X.X) (x, PUnit.unit)
  mul_assoc x y z := by
    change (ConcreteCategory.hom (μ[X.X] ▷ X.X ≫ μ[X.X])) ((x, y), z) =
      (ConcreteCategory.hom ((α_ X.X X.X X.X).hom ≫ X.X ◁ μ[X.X] ≫ μ[X.X])) ((x, y), z)
    exact ConcreteCategory.congr_hom (MonObj.mul_assoc X.X) ((x, y), z)
  inv_mul_cancel x := by
    change (ConcreteCategory.hom (lift ι[X.X] (𝟙 X.X) ≫ μ[X.X])) x =
      (ConcreteCategory.hom (toUnit X.X ≫ η[X.X])) x
    exact ConcreteCategory.congr_hom (GrpObj.left_inv X.X) x

/-- A continuous group homomorphism realizes a monoid-homomorphic `TopCat` map between group
objects. -/
@[stacks 0B1Z "continuous homomorphisms of topological group objects"]
instance instContinuousMonoidHomIsMonHom {X Y : Grp TopCat.{u}} (f : X.X →ₜ* Y.X) :
    IsMonHom (ConcreteCategory.ofHom (C := TopCat) f.toContinuousMap) where
  one_hom := by
    ext x
    change f 1 = (1 : Y.X)
    simp
  mul_hom := by
    ext x
    change f (x.1 * x.2) = f x.1 * f x.2
    simp

/-- The continuous group homomorphism underlying a morphism of topological group objects. -/
@[stacks 0B1Z "underlying continuous homomorphism of a topological group morphism"]
abbrev homToContinuousMonoidHom {X Y : Grp TopCat.{u}} (f : X ⟶ Y) :
    X.X →ₜ* Y.X where
  toFun := f.hom.hom
  map_one' := by
    change (ConcreteCategory.hom (η[X.X] ≫ f.hom.hom)) PUnit.unit =
      (ConcreteCategory.hom η[Y.X]) PUnit.unit
    exact ConcreteCategory.congr_hom (IsMonHom.one_hom f.hom.hom) PUnit.unit
  map_mul' x y := by
    change (ConcreteCategory.hom (μ[X.X] ≫ f.hom.hom)) (x, y) =
      (ConcreteCategory.hom ((f.hom.hom ⊗ₘ f.hom.hom) ≫ μ[Y.X])) (x, y)
    exact ConcreteCategory.congr_hom (IsMonHom.mul_hom f.hom.hom) (x, y)
  continuous_toFun := (TopCat.Hom.hom f.hom.hom).continuous

/-- Topological group objects form a concrete category over continuous group homomorphisms. -/
@[stacks 0B20 "concrete realization of the category of topological groups"]
instance instConcreteCategory : ConcreteCategory (Grp TopCat.{u}) (fun X Y ↦ X.X →ₜ* Y.X) where
  hom := homToContinuousMonoidHom
  ofHom := by
    intro X Y f
    exact Grp.homMk (ConcreteCategory.ofHom (C := TopCat) f.toContinuousMap)
  hom_ofHom := by
    intro X Y f
    ext x
    rfl
  ofHom_hom := by
    intro X Y f
    apply Grp.hom_ext
    apply TopCat.ext
    intro x
    rfl

/-- The forgetful functor from topological group objects to ordinary groups. -/
@[stacks 0B20 "forgetful functor from topological groups to groups"]
noncomputable instance hasForget₂GrpCat :
    HasForget₂ (Grp TopCat.{u}) GrpCat.{u} :=
  { forget₂ := by
      -- Local instance justification (instance diamond): the monoidal structure comes from a
      -- chosen finite-product presentation and must not become a competing global choice.
      let _ : (forget TopCat.{u}).Monoidal :=
        Functor.Monoidal.ofChosenFiniteProducts (forget TopCat.{u})
      exact (forget TopCat.{u}).mapGrp ⋙ grpTypeEquivalenceGrp.functor
    forget_comp := rfl }

end GrpTopCat
