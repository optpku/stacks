/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Scheme
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.TensorWithObject.Derived.Functor
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Quasicoherent
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Basic

@[expose] public section

open CategoryTheory
open CategoryTheory.CochainComplex.Enriched
open SheafOfModules.RingedSite
open SheafOfModules.RingedSite.TensorWithObject

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

variable {X : Scheme.{u}}
variable (K : CochainComplex X.toRingedSpace.Modules ℤ)

/-- If every homology sheaf of `K` is quasicoherent, then the canonical derived tensor
functor associated to `K` takes every object to a derived module with quasicoherent
cohomology. -/
theorem tensorFunctor_mem
    (hK : ∀ n : ℤ, RingedSpace.quasiCoherentModuleProperty X.toRingedSpace
      (K.homology n))
    (M : DifferentialGradedModule.Derived.Category.{0, u} (endDGA.{u, u} K)) :
    DerivedCategory.cohomologyIn
      (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)
      ((SheafOfModules.RingedSite.TensorWithObject.Derived.tensorFunctor K).obj M) := sorry

/-- The canonical derived tensor functor associated to `K`, factored through the full
subcategory of derived modules with quasicoherent cohomology. -/
noncomputable def tensorFunctor
    (hK : ∀ n : ℤ, RingedSpace.quasiCoherentModuleProperty X.toRingedSpace
      (K.homology n)) :
    DifferentialGradedModule.Derived.Category.{0, u} (endDGA.{u, u} K) ⥤
      DerivedCategory.CohomologyIn
        (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace) :=
  (DerivedCategory.cohomologyIn
      (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)).lift
    (SheafOfModules.RingedSite.TensorWithObject.Derived.tensorFunctor K)
    (tensorFunctor_mem K hK)

/-- Forgetting the quasicoherent-cohomology condition on an object in the factorized
derived tensor functor recovers the corresponding canonical derived tensor object. -/
@[simp]
theorem tensorFunctor_obj
    (hK : ∀ n : ℤ, RingedSpace.quasiCoherentModuleProperty X.toRingedSpace
      (K.homology n))
    (M : DifferentialGradedModule.Derived.Category.{0, u} (endDGA.{u, u} K)) :
    ((tensorFunctor K hK).obj M).obj =
      (SheafOfModules.RingedSite.TensorWithObject.Derived.tensorFunctor K).obj M := sorry

/-- Forgetting the quasicoherent-cohomology condition on a map in the factorized
derived tensor functor recovers the corresponding canonical derived tensor map. -/
@[simp]
theorem tensorFunctor_map
    (hK : ∀ n : ℤ, RingedSpace.quasiCoherentModuleProperty X.toRingedSpace
      (K.homology n))
    {M N : DifferentialGradedModule.Derived.Category.{0, u} (endDGA.{u, u} K)}
    (f : M ⟶ N) :
    ((tensorFunctor K hK).map f).hom =
      (SheafOfModules.RingedSite.TensorWithObject.Derived.tensorFunctor K).map f := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh
