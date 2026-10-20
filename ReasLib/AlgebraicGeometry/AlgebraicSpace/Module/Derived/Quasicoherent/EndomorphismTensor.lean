/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.TensorWithObject.Derived.Functor
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RingedSite.CommRing
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.CohomologyIn

/-!
# Derived tensor with a quasi-coherent-cohomology complex on an algebraic space

The canonical DG derived-tensor functor `- ⊗^L_(endDGA K) K` of a complex of `𝒪_X`-modules
lands in `D_QCoh` whenever the homology sheaves of `K` are quasi-coherent.
-/

@[expose] public section

open AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open CategoryTheory
open SheafOfModules.RingedSite
open SheafOfModules.RingedSite.TensorWithObject

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

variable {S : Scheme.{u}} {X : AlgebraicSpace S}
variable (K : CochainComplex (RingedSite.ModuleCat.{u + 1} (commRingedSiteLift X)) ℤ)

/-- If every homology sheaf of `K` is quasi-coherent, then the canonical derived tensor
functor associated to `K` takes every object to a derived module with quasi-coherent
cohomology. -/
theorem tensorFunctor_mem
    (hK : ∀ n : ℤ,
      SheafOfModules.isQuasicoherent (commRingedSiteLift X).structureSheaf (K.homology n))
    (M : DifferentialGradedModule.Derived.Category.{0, u + 1} (endDGA.{u + 1, u} K)) :
    RingedSite.Hom.moduleCohomologyIn.{u + 1} (commRingedSiteLift X)
      (SheafOfModules.isQuasicoherent (commRingedSiteLift X).structureSheaf)
      ((SheafOfModules.RingedSite.TensorWithObject.Derived.tensorFunctor K).obj M) :=
  sorry

/-- The canonical derived tensor functor associated to `K`, factored through the full
subcategory of derived modules with quasi-coherent cohomology. -/
noncomputable def tensorFunctor
    (hK : ∀ n : ℤ,
      SheafOfModules.isQuasicoherent (commRingedSiteLift X).structureSheaf (K.homology n)) :
    DifferentialGradedModule.Derived.Category.{0, u + 1} (endDGA.{u + 1, u} K) ⥤
      RingedSite.Hom.ModuleCohomologyIn.{u + 1} (commRingedSiteLift X)
        (SheafOfModules.isQuasicoherent (commRingedSiteLift X).structureSheaf) :=
  (RingedSite.Hom.moduleCohomologyIn.{u + 1} (commRingedSiteLift X)
      (SheafOfModules.isQuasicoherent (commRingedSiteLift X).structureSheaf)).lift
    (SheafOfModules.RingedSite.TensorWithObject.Derived.tensorFunctor K)
    (tensorFunctor_mem K hK)

/-- Forgetting the quasi-coherent-cohomology condition on an object in the factorized
derived tensor functor recovers the corresponding canonical derived tensor object. -/
@[simp]
theorem tensorFunctor_obj
    (hK : ∀ n : ℤ,
      SheafOfModules.isQuasicoherent (commRingedSiteLift X).structureSheaf (K.homology n))
    (M : DifferentialGradedModule.Derived.Category.{0, u + 1} (endDGA.{u + 1, u} K)) :
    ((tensorFunctor K hK).obj M).obj =
      (SheafOfModules.RingedSite.TensorWithObject.Derived.tensorFunctor K).obj M :=
  rfl

/-- Forgetting the quasi-coherent-cohomology condition on a map in the factorized
derived tensor functor recovers the corresponding canonical derived tensor map. -/
@[simp]
theorem tensorFunctor_map
    (hK : ∀ n : ℤ,
      SheafOfModules.isQuasicoherent (commRingedSiteLift X).structureSheaf (K.homology n))
    {M N : DifferentialGradedModule.Derived.Category.{0, u + 1} (endDGA.{u + 1, u} K)}
    (f : M ⟶ N) :
    ((tensorFunctor K hK).map f).hom =
      (SheafOfModules.RingedSite.TensorWithObject.Derived.tensorFunctor K).map f :=
  rfl

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
