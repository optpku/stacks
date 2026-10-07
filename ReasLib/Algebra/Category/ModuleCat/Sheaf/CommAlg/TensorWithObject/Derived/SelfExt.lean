module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.CommAlg.TensorWithObject.Derived.Regular
public import ReasLib.Algebra.Homology.CochainComplex.DifferentialGraded.HomComplex.DerivedHom.Over
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Derived.Regular
public import ReasLib.CategoryTheory.Shift.ShiftedHom.Functor

/-!
# Self-Ext comparison for coefficient-generic derived tensoring

This file compares the canonical `R`-linear self-Ext map of `K` with the map obtained by
applying derived tensor to shifted self-Homs of the regular `endDGA K`-module.
-/

@[expose] public section

noncomputable section

universe r u v w z

open CategoryTheory
open DifferentialGradedCategory
open scoped DifferentialGradedCategory SheafOfModules.CommAlg

namespace SheafOfModules.CommAlg.TensorWithObject.Derived

variable {R : Type r} [CommRing R]
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ (CommAlgCat.{w} R) CommRingCat.{w})]
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [UnivLE.{max u v, max u z}]
variable [HasWeakSheafify J AddCommGrpCat.{max u z}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u z}]
variable {O : Sheaf J (CommAlgCat.{w} R)}

/-- The canonical `R`-linear map on shifted self-Homs of the regular DG module induced by
derived tensoring with `K`. -/
@[stacks 09LZ "arbitrary-ring derived tensor on regular self-Ext"]
noncomputable abbrev regularShiftMap
    (K : Complex.{r, u, v, w, max u z} O) (n : ℤ) :
    ShiftedHom
        (DifferentialGradedModule.Derived.regularObject (endDGA K))
        (DifferentialGradedModule.Derived.regularObject (endDGA K)) n →ₗ[R]
      ShiftedHom
        ((tensorFunctor K).obj
          (DifferentialGradedModule.Derived.regularObject (endDGA K)))
        ((tensorFunctor K).obj
          (DifferentialGradedModule.Derived.regularObject (endDGA K))) n :=
  (tensorFunctor K).shiftedHomLinearMap (R := R)
    (DifferentialGradedModule.Derived.regularObject (endDGA K))
    (DifferentialGradedModule.Derived.regularObject (endDGA K)) n

/-- The regular-module self-Ext comparison commutes with derived tensoring and the canonical
comparison from the tensor image of the regular module to `K`. -/
@[reassoc, stacks 09LZ "compatibility of arbitrary-ring regular and enriched self-Ext"]
theorem regularSelfExt_comm
    (K : Complex.{r, u, v, w, max u z} O) (n : ℤ)
    (x : (endDGA K).homology n) :
    ShiftedHom.map
          (DifferentialGradedModule.Derived.regularSelfExtLinearMap (endDGA K) n x)
          (tensorFunctor K) ≫
        (shiftFunctor _ n).map (regularComparison K) =
      regularComparison K ≫
        CategoryTheory.CochainComplex.Enriched.Over.RHom.selfExtLinearMap
          (R := R) K n x := sorry

/-- The enriched self-Ext comparison for `K` is bijective exactly when derived tensoring is
bijective on the degree-`n` self-Hom of the regular DG module. -/
@[stacks 09LZ "arbitrary-ring self-Ext comparison via the regular DG module"]
theorem regularShiftMap_bijective_iff
    (K : Complex.{r, u, v, w, max u z} O) (n : ℤ) :
    Function.Bijective (regularShiftMap K n) ↔
      Function.Bijective
        (CategoryTheory.CochainComplex.Enriched.Over.RHom.selfExtLinearMap
          (R := R) K n) := sorry

end SheafOfModules.CommAlg.TensorWithObject.Derived
