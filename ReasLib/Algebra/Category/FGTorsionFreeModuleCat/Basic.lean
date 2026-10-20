/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.CategoryTheory.ObjectProperty.CompleteLattice
public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
public import Mathlib.CategoryTheory.Preadditive.Basic
public import Mathlib.CategoryTheory.Preadditive.Biproducts

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

variable (R : Type u) [CommRing R]

/-- Torsion-free modules, as a property of objects of `ModuleCat R`. -/
def ModuleCat.isTorsionFree : ObjectProperty (ModuleCat.{v} R) :=
  fun M ↦ Module.IsTorsionFree R M

/-- A bundled module is torsion-free iff the module typeclass holds. -/
theorem ModuleCat.isTorsionFree_iff (M : ModuleCat.{v} R) :
    ModuleCat.isTorsionFree R M ↔ Module.IsTorsionFree R M :=
  Iff.rfl

/-- Finitely generated torsion-free modules, as a property of objects of `ModuleCat R`. -/
def ModuleCat.isFGTorsionFree : ObjectProperty (ModuleCat.{v} R) :=
  ModuleCat.isFG.{v} R ⊓ ModuleCat.isTorsionFree.{v} R

/-- A bundled module is finitely generated and torsion-free iff both module typeclasses hold. -/
theorem ModuleCat.isFGTorsionFree_iff (M : ModuleCat.{v} R) :
    ModuleCat.isFGTorsionFree R M ↔ Module.Finite R M ∧ Module.IsTorsionFree R M :=
  Iff.rfl

/-- The category of finitely generated torsion-free modules over `R`. -/
abbrev FGTorsionFreeModuleCat :=
  (ModuleCat.isFGTorsionFree.{v} R).FullSubcategory

variable {R}

/-- The underlying carrier type of a finitely generated torsion-free module. -/
@[reducible]
def FGTorsionFreeModuleCat.carrier (M : FGTorsionFreeModuleCat.{v} R) : Type v :=
  M.obj.carrier

/-- Coerce an object of `FGTorsionFreeModuleCat` to its underlying carrier type. -/
instance FGTorsionFreeModuleCat.instCoeSort : CoeSort (FGTorsionFreeModuleCat.{v} R) (Type v) :=
  ⟨FGTorsionFreeModuleCat.carrier⟩

attribute [coe] FGTorsionFreeModuleCat.carrier

/-- Objects of `FGTorsionFreeModuleCat` are finitely generated. -/
instance FGTorsionFreeModuleCat.instModuleFinite (M : FGTorsionFreeModuleCat.{v} R) : Module.Finite R M :=
  M.property.1

/-- Objects of `FGTorsionFreeModuleCat` are torsion-free. -/
instance FGTorsionFreeModuleCat.instModuleIsTorsionFree (M : FGTorsionFreeModuleCat.{v} R) : Module.IsTorsionFree R M :=
  M.property.2

namespace FGTorsionFreeModuleCat

variable (R) in
/-- Lift an unbundled finitely generated torsion-free module to `FGTorsionFreeModuleCat R`. -/
abbrev of (V : Type v) [AddCommGroup V] [Module R V] [Module.Finite R V]
    [Module.IsTorsionFree R V] : FGTorsionFreeModuleCat.{v} R :=
  ⟨ModuleCat.of R V, ⟨inferInstanceAs (Module.Finite R V),
    inferInstanceAs (Module.IsTorsionFree R V)⟩⟩

/-- Lift a linear map between finitely generated torsion-free modules. -/
abbrev ofHom {V W : Type v} [AddCommGroup V] [Module R V] [Module.Finite R V]
    [Module.IsTorsionFree R V] [AddCommGroup W] [Module R W] [Module.Finite R W]
    [Module.IsTorsionFree R W] (f : V →ₗ[R] W) : of R V ⟶ of R W :=
  ObjectProperty.homMk (ModuleCat.ofHom f)

variable (R) in
/-- The zero module is finitely generated and torsion-free. -/
instance instContainsZero [IsDomain R] :
    (ModuleCat.isFGTorsionFree.{v} R).ContainsZero :=
  sorry

variable (R) in
/-- Finite products of finitely generated torsion-free modules remain finitely generated and
torsion-free. -/
instance instIsClosedUnderFiniteProducts [IsDomain R] :
    (ModuleCat.isFGTorsionFree.{v} R).IsClosedUnderFiniteProducts :=
  sorry

variable (R) in
/-- Over a domain, the category of finitely generated torsion-free modules has finite biproducts. -/
instance instHasFiniteBiproducts [IsDomain R] :
    HasFiniteBiproducts (FGTorsionFreeModuleCat.{v} R) :=
  HasFiniteBiproducts.of_hasFiniteProducts

end FGTorsionFreeModuleCat
