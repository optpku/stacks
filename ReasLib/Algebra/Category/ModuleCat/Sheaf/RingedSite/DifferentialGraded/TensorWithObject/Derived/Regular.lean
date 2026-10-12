/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.TensorWithObject.Derived.Functor
public import ReasLib.Algebra.Homology.CochainComplex.DifferentialGraded.Homotopy.Derived
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Derived.Regular
public import ReasLib.CategoryTheory.Functor.Derived.ComputesAt

/-!
# The regular DG module under derived tensor

The regular right module over `endDGA K` computes the derived tensor functor.  This file owns the
canonical comparison from its tensor image to the canonical derived object represented by `K`,
including the compactness transport needed by the compact-generator criterion.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.CochainComplex.Enriched
open DifferentialGradedCategory
open scoped DifferentialGradedCategory

namespace SheafOfModules.RingedSite.TensorWithObject.Derived

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable {O : Sheaf J CommRingCat.{max u v}}

/-- The regular module computes the concrete total left derived tensor functor. -/
@[stacks 09LZ "regular module computes derived tensor"]
theorem regularComputesTensor (K : Complex (J := J) (O := O)) :
    Functor.LeftDerived.ComputesAt (tensorSourceFunctor K)
      (DifferentialGradedModule.quasiIso (endDGA K))
      (⟨(endDGA K).regularModule⟩ :
        DifferentialGradedCategory.K ℤ (Modules K)) := sorry

/-- The derived-tensor comparison is invertible on the regular module. -/
@[stacks 09LZ "regular module tensor counit is an isomorphism"]
theorem tensorCounit_regular_isIso (K : Complex (J := J) (O := O)) :
    IsIso ((tensorCounit K).app
      (⟨(endDGA K).regularModule⟩ :
        DifferentialGradedCategory.K ℤ (Modules K))) := sorry

/-- The canonical comparison from the image of the regular derived DG module to the derived
object represented by `K`.  Its morphism data is explicit; invertibility is recorded separately
by `regularComparison_isIso`. -/
@[stacks 09LZ "regular-module comparison for derived tensor"]
def regularComparison (K : Complex (J := J) (O := O)) :
    (tensorFunctor K).obj
        (DifferentialGradedModule.Derived.regularObject (endDGA K)) ⟶
      (@DerivedCategory.Q _ _ _
        (SheafOfModules.RingedSite.moduleCategoryHasDerivedCategory
          (J := J) (𝒪 := O))).obj K :=
  ((tensorFunctor K).mapIso
      ((DifferentialGradedModule.Derived.Q (endDGA K)).mapIso
        (DifferentialGradedModule.Derived.regularZeroIso (endDGA K)))).hom ≫
    (tensorCounit K).app
      (⟨(endDGA K).regularModule⟩ :
        DifferentialGradedCategory.K ℤ (Modules K)) ≫
    ((@DerivedCategory.Qh _ _ _
      (SheafOfModules.RingedSite.moduleCategoryHasDerivedCategory
        (J := J) (𝒪 := O)) :
      TensorWithObject.TargetHomotopy (J := J) (O := O) ⥤
        RingedSiteDerived.max J O).mapIso
      ((HomotopyCategory.quotient
        (ringedSiteModuleCategory.{u, v, max u v, max u v} J O)
        (ComplexShape.up ℤ)).mapIso (TensorWithObject.objRegularIso K))).hom ≫
    (@CochainComplex.Enriched.derivedQObjIso _ _ _
      (SheafOfModules.RingedSite.moduleCategoryHasDerivedCategory
        (J := J) (𝒪 := O)) K).hom

/-- The canonical regular-module comparison for derived tensoring is invertible. -/
@[stacks 09LZ "regular-module derived tensor comparison is an isomorphism"]
theorem regularComparison_isIso (K : Complex (J := J) (O := O)) :
    IsIso (regularComparison K) := sorry

/-- The named isomorphism represented by the regular-module comparison. -/
@[stacks 09LZ "regular-module derived tensor comparison isomorphism"]
noncomputable def regularComparisonIso (K : Complex (J := J) (O := O)) :
    (tensorFunctor K).obj
        (DifferentialGradedModule.Derived.regularObject (endDGA K)) ≅
      (@DerivedCategory.Q _ _ _
        (SheafOfModules.RingedSite.moduleCategoryHasDerivedCategory
          (J := J) (𝒪 := O))).obj K :=
  @asIso _ _ _ _ (regularComparison K) (regularComparison_isIso K)

/-- Compactness of `K` transports across `regularComparison` to the image of the regular DG
module. -/
@[stacks 09LZ "compactness transported along regular tensor comparison"]
theorem regularImage_isCompact
    (K : Complex (J := J) (O := O))
    (h_compact : IsCompactObject
      ((@DerivedCategory.Q _ _ _
        (SheafOfModules.RingedSite.moduleCategoryHasDerivedCategory
          (J := J) (𝒪 := O))).obj K)) :
    IsCompactObject
      ((tensorFunctor K).obj
        (DifferentialGradedModule.Derived.regularObject (endDGA K))) := sorry

end SheafOfModules.RingedSite.TensorWithObject.Derived
