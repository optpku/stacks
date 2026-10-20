/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.TensorWithObject.Derived.Regular
public import ReasLib.Algebra.Homology.CochainComplex.DifferentialGraded.HomComplex.DerivedHom
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Derived.Regular
public import ReasLib.CategoryTheory.Shift.ShiftedHom.Functor

/-!
# Self-Ext comparison for derived tensoring

This file compares the canonical cohomological self-Ext map for `K` with the map obtained by
applying derived tensor to the shifted self-Homs of the regular `endDGA K`-module.  The comparison
is expressed against the generic owners for enriched Hom cohomology and regular DG-module
self-extensions.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory
open CategoryTheory.CochainComplex.Enriched
open DifferentialGradedCategory
open scoped DifferentialGradedCategory

namespace SheafOfModules.RingedSite.TensorWithObject.Derived

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable {O : Sheaf J CommRingCat.{max u v}}

/-- The canonical linear map on shifted self-Homs of the regular DG module induced by derived
tensoring with `K`. -/
@[stacks 09LZ "derived tensor on regular self-Ext"]
noncomputable abbrev regularShiftMap
    (K : Complex (J := J) (O := O)) (n : ℤ) :
    ShiftedHom
        (DifferentialGradedModule.Derived.regularObject (endDGA K))
        (DifferentialGradedModule.Derived.regularObject (endDGA K)) n →ₗ[ℤ]
      ShiftedHom
        ((tensorFunctor K).obj
          (DifferentialGradedModule.Derived.regularObject (endDGA K)))
        ((tensorFunctor K).obj
          (DifferentialGradedModule.Derived.regularObject (endDGA K))) n :=
  (tensorFunctor K).shiftedHomLinearMap (R := ℤ)
    (DifferentialGradedModule.Derived.regularObject (endDGA K))
    (DifferentialGradedModule.Derived.regularObject (endDGA K)) n

/-- The regular-module self-Ext comparison commutes with derived tensoring and the canonical
comparison from the tensor image of the regular module to `K`. -/
@[reassoc, stacks 09LZ "compatibility of regular and enriched self-Ext"]
theorem regularSelfExt_comm
    (K : Complex (J := J) (O := O)) (n : ℤ) (x : (endDGA K).homology n) :
    ShiftedHom.map
          (DifferentialGradedModule.Derived.regularSelfExtLinearMap (endDGA K) n x)
          (tensorFunctor K) ≫
        (shiftFunctor _ n).map (regularComparison K) =
      regularComparison K ≫ CochainComplex.Enriched.selfExtLinearMap K n x := sorry

/-- The enriched self-Ext comparison for `K` is bijective exactly when derived tensoring is
bijective on the degree-`n` self-Hom of the regular DG module. -/
@[stacks 09LZ "self-Ext comparison via the regular DG module"]
theorem regularShiftMap_bijective_iff
    (K : Complex (J := J) (O := O)) (n : ℤ) :
    Function.Bijective (regularShiftMap K n) ↔
      Function.Bijective (CochainComplex.Enriched.selfExtLinearMap K n) := sorry

end SheafOfModules.RingedSite.TensorWithObject.Derived
