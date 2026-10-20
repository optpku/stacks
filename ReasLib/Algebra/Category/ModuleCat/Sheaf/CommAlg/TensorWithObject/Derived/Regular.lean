module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.CommAlg.TensorWithObject.Derived.Functor
public import ReasLib.Algebra.Homology.CochainComplex.DifferentialGraded.Homotopy.Derived
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Derived.Regular
public import ReasLib.CategoryTheory.Functor.Derived.ComputesAt

/-!
# The regular DG module under derived tensor over an algebra sheaf

The regular right module over `endDGA K` computes the coefficient-generic derived tensor
functor.  This file owns the canonical comparison from its image to the derived object
represented by `K`, together with the compactness transport used by generator arguments.
-/

@[expose] public section

noncomputable section

universe r u v w z

open CategoryTheory CategoryTheory.Limits
open DifferentialGradedCategory
open scoped DifferentialGradedCategory SheafOfModules.CommAlg

namespace SheafOfModules.CommAlg.TensorWithObject.Derived

-- Use the existing standard localization for the actual underlying ring-sheaf carrier.
attribute [local instance] RingedSite.Hom.RingPresentation.moduleHasDerivedCategory

variable {R : Type r} [CommRing R]
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ (CommAlgCat.{w} R) CommRingCat.{w})]
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [UnivLE.{max u v, max u z}]
variable [HasWeakSheafify J AddCommGrpCat.{max u z}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u z}]
variable {O : Sheaf J (CommAlgCat.{w} R)}

/-- The regular module computes the total left-derived tensor functor. -/
@[stacks 09LZ "regular module computes arbitrary-ring derived tensor"]
instance regularComputesTensor (K : Complex.{r, u, v, w, max u z} O) :
    Functor.LeftDerived.ComputesAt (tensorSourceFunctor K)
      (DifferentialGradedModule.quasiIso (endDGA K))
      (⟨(endDGA K).regularModule⟩ :
        DifferentialGradedCategory.K R (TensorWithObject.Modules K)) := sorry

/-- The derived-tensor comparison is invertible on the regular module. -/
@[stacks 09LZ "regular module arbitrary-ring tensor counit is an isomorphism"]
instance tensorCounit_regular_isIso (K : Complex.{r, u, v, w, max u z} O) :
    IsIso ((tensorCounit K).app
      (⟨(endDGA K).regularModule⟩ :
        DifferentialGradedCategory.K R (TensorWithObject.Modules K))) := sorry

/-- The canonical comparison from the derived tensor image of the regular DG module to the
derived object represented by `K`. -/
@[stacks 09LZ "arbitrary-ring regular-module comparison for derived tensor"]
def regularComparison (K : Complex.{r, u, v, w, max u z} O) :
    (tensorFunctor K).obj
        (DifferentialGradedModule.Derived.regularObject (endDGA K)) ⟶
      DerivedCategory.Q.obj K :=
  ((tensorFunctor K).mapIso
      ((DifferentialGradedModule.Derived.Q (endDGA K)).mapIso
        (DifferentialGradedModule.Derived.regularZeroIso (endDGA K)))).hom ≫
    (tensorCounit K).app
      (⟨(endDGA K).regularModule⟩ :
        DifferentialGradedCategory.K R (TensorWithObject.Modules K)) ≫
    (DerivedCategory.Qh.mapIso
      ((HomotopyCategory.quotient
        (SheafOfModules.CommAlg.Modules.{r, u, v, w, max u z} O)
        (ComplexShape.up ℤ)).mapIso (TensorWithObject.objRegularIso K))).hom ≫
    (SheafOfModules.CommAlg.Derived.objIso O K).hom

/-- The canonical regular-module comparison for derived tensoring is invertible. -/
@[stacks 09LZ "arbitrary-ring regular derived tensor comparison is an isomorphism"]
instance regularComparison_isIso (K : Complex.{r, u, v, w, max u z} O) :
    IsIso (regularComparison K) := sorry

/-- The named isomorphism represented by the regular-module comparison. -/
@[stacks 09LZ "arbitrary-ring regular derived tensor comparison isomorphism"]
noncomputable def regularComparisonIso
    (K : Complex.{r, u, v, w, max u z} O) :
    (tensorFunctor K).obj
        (DifferentialGradedModule.Derived.regularObject (endDGA K)) ≅
      DerivedCategory.Q.obj K :=
  asIso (regularComparison K)

/-- Compactness of `K` transports across the regular-module comparison to the image of the
regular DG module. -/
@[stacks 09LZ "compactness transported along arbitrary-ring regular tensor comparison"]
theorem regularImage_isCompact
    (K : Complex.{r, u, v, w, max u z} O)
    (h_compact : IsCompactObject (DerivedCategory.Q.obj K)) :
    IsCompactObject
      ((tensorFunctor K).obj
        (DifferentialGradedModule.Derived.regularObject (endDGA K))) := sorry

end SheafOfModules.CommAlg.TensorWithObject.Derived
