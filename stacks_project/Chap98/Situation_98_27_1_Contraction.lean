/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Lemma_67_24_2_FieldPoints
public import stacks_project.Chap67.Remark_67_12_5_Opens
public import stacks_project.Chap87.Lemma_87_34_3_Reduction
public import stacks_project.Chap88.Definition_88_24_1_Modification
public import stacks_project.Chap88.«88_27_0_1_Completion»

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Contraction

/-!
# Standing data for Artin contractions

A locally Noetherian base, an algebraic space locally of finite type, a closed
subset of its points, a locally Noetherian formal algebraic space whose
canonical reduction is locally of finite type, and a formal modification from
the completion along that closed subset.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace ContractionSituation

variable {S : Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian S]

/-- The reduction of the stored formal algebraic space, with its reduced space,
inclusion, representable thickening, and unique factorization property. -/
@[reducible] def reduction_W (σ : ContractionSituation S) :
    @FormalAlgebraicSpace.Reduction S σ.W σ.isFormal_W :=
  @FormalAlgebraicSpace.Reduction.mk S σ.W σ.isFormal_W
    (@FormalAlgebraicSpace.ReductionData.space S σ.W σ.isFormal_W σ.reductionData_W)
    (@FormalAlgebraicSpace.ReductionData.ι S σ.W σ.isFormal_W σ.reductionData_W)
    (@FormalAlgebraicSpace.ReductionData.isReduced S σ.W σ.isFormal_W σ.reductionData_W)
    (@FormalAlgebraicSpace.ReductionData.representable S σ.W σ.isFormal_W σ.reductionData_W)
    (fun {_} ξ ↦
    { toIsClosedImmersion :=
        (@FormalAlgebraicSpace.ReductionData.isThickening S σ.W σ.isFormal_W
          σ.reductionData_W _ ξ).1
      toSurjective :=
        ⟨(@FormalAlgebraicSpace.ReductionData.isThickening S σ.W σ.isFormal_W
          σ.reductionData_W _ ξ).2⟩ })
    (@FormalAlgebraicSpace.ReductionData.liftUnique S σ.W σ.isFormal_W σ.reductionData_W)

/-- Package an algebraic space `X'` locally of finite type over `S`, a closed
subset `T'` of `Points X'`, a locally Noetherian formal algebraic space `W`
with canonical reduction locally of finite type over `S`, and a formal
modification from the completion of `X'` along `T'`. -/
def of (X' : AlgebraicSpace S) [LocallyOfFiniteType (toBase X')]
    [IsLocallyNoetherian X'] (T' : Closeds (Points X'))
    (W : (Over S)ᵒᵖ ⥤ Type u)
    [FormalAlgebraicSpace.IsFormalAlgebraicSpace W]
    [FormalAlgebraicSpace.IsLocallyNoetherian W]
    [FormalAlgebraicSpace.Reduction W]
    [LocallyOfFiniteType (toBase (FormalAlgebraicSpace.reduction W))]
    (g : completionAlong X' T' ⟶ W)
    [FormalAlgebraicSpace.LocallyOfFiniteType g]
    [@FormalAlgebraicSpace.FormalModification S (completionAlong X' T') W g
      (completionAlong.instIsFormalAlgebraicSpace X' T') inferInstance
      (completionAlong.instIsLocallyNoetherian X' T') inferInstance inferInstance] :
    ContractionSituation S :=
  ofData X' T' W (inferInstance : FormalAlgebraicSpace.Reduction W).toReductionData
    (locallyOfFiniteType_red :=
      (inferInstance : LocallyOfFiniteType (toBase (FormalAlgebraicSpace.reduction W)))) g

/-- A contraction situation records that its algebraic space is locally of
finite type and locally Noetherian, its formal algebraic space is locally
Noetherian with reduction locally of finite type, and its map is a formal
modification. -/
theorem spec (σ : ContractionSituation S) :
    LocallyOfFiniteType (toBase σ.X') ∧ IsLocallyNoetherian σ.X' ∧
      FormalAlgebraicSpace.IsFormalAlgebraicSpace σ.W ∧
      @FormalAlgebraicSpace.IsLocallyNoetherian S σ.W σ.isFormal_W ∧
      LocallyOfFiniteType (toBase
        (@FormalAlgebraicSpace.reduction S σ.W σ.isFormal_W σ.reduction_W)) ∧
      @FormalAlgebraicSpace.FormalModification S (completionAlong σ.X' σ.T')
        σ.W σ.g
        (@completionAlong.instIsFormalAlgebraicSpace S σ.X'
          σ.isLocallyNoetherian_X' σ.T') σ.isFormal_W
        (@completionAlong.instIsLocallyNoetherian S σ.X'
          σ.isLocallyNoetherian_X' σ.T')
        σ.isLocallyNoetherian_W σ.locallyOfFiniteType_g := by
  exact ⟨σ.locallyOfFiniteType_X', σ.isLocallyNoetherian_X', σ.isFormal_W,
    σ.isLocallyNoetherian_W, σ.locallyOfFiniteType_red, σ.isFormalModification⟩

end ContractionSituation

end AlgebraicGeometry.AlgebraicSpace
