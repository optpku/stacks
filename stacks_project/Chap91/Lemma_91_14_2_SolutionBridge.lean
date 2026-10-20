/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module
public import stacks_project.Chap91.Lemma_91_14_2_SmallKernel
public import stacks_project.Chap76.Lemma_76_9_7
@[expose] public section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace AlgebraicGeometry.AlgebraicSpace.SquareZeroExtension
open SheafOfModules.RingedSite
noncomputable section
universe u
namespace AlgebraicGeometry.AlgebraicSpace.Thickening.FlatLift
variable {S : Scheme.{u}} {Y Y' X : AlgebraicSpace S}
variable {t : Y ⟶ Y'} [IsFirstOrderThickening t] {f : X ⟶ Y} [Flat f]

instance baseProjection_surjective : IsLocallySurjective (inverseImageThickeningMap (t := t) (f := f)) := sorry

theorem baseProjection_squareZero : KernelIdeal.IsSquareZero
    (inverseImageThickeningMap (t := t) (f := f)) := sorry

theorem baseProjection_comp : inverseImageThickeningMap (t := t) (f := f) ≫
    commInverseImageStructureSheafMap f = commInverseImageStructureSheafMap (f ≫ t) := sorry

theorem liftAlgebra_commutes (L : FlatLift t f) :
    liftAlgebraOver L ≫ liftAlgebraProj L =
      inverseImageThickeningMap (t := t) (f := f) ≫ commInverseImageStructureSheafMap f := sorry

/-- The actual induced map on base kernels, expressed in the geometrically fixed coefficient module. -/
def equationMap (L : FlatLift t f) :=
  FirstOrderThickening.kernelMapOf.{u + 1, u, u}
    (inverseImageThickeningMap (t := t) (f := f)) (baseProjection_squareZero (t := t) (f := f))
    (commInverseImageStructureSheafMap f) (liftAlgebraProj L) (liftAlgebra_squareZero L)
    (KernelIdeal.quotientComparison_isIso (liftAlgebraProj L)) (liftAlgebraOver L)
    (liftAlgebra_commutes L) ≫
      (restrictionAlong (commInverseImageStructureSheafMap f)).map (SmallKernel.kernelIso L).hom

/-- All cartesian lifts induce the same base-kernel map: their kernel identifications
were constructed from the same geometric pullback inclusion, not chosen independently. -/
theorem equationMap_eq (L₁ L₂ : FlatLift t f) : equationMap L₁ = equationMap L₂ := sorry

abbrev LiftSolution (L : FlatLift t f) :=
  FirstOrderThickening.Solution.{u + 1, u, u}
    (inverseImageThickeningMap (t := t) (f := f)) (baseProjection_squareZero (t := t) (f := f))
    (commInverseImageStructureSheafMap f) (pulledConormal t f) (equationMap L)

/-- Rebundle a second actual flat lift as a solution of the fixed basepoint equation. -/
def toSolution (L₀ L : FlatLift t f) : LiftSolution L₀ where
  middle := liftAlgebra L
  proj := liftAlgebraProj L
  structureMap := liftAlgebraOver L
  proj_locallySurjective := inferInstance
  proj_squareZero := liftAlgebra_squareZero L
  proj_quotient_isIso := KernelIdeal.quotientComparison_isIso (liftAlgebraProj L)
  commutes := liftAlgebra_commutes L
  kernelIso := SmallKernel.kernelIso L
  induces_c := equationMap_eq L L₀

/-- The middle algebra is the real inverse image of the ambient structure sheaf. -/
@[simp] theorem toSolution_middle (L₀ L : FlatLift t f) :
    (toSolution L₀ L).middle = liftAlgebra L := rfl

variable (L₀ : FlatLift t f) (sol : LiftSolution L₀)

-- Local instance justification (proof-local temporary data): the solution record supplies the exact projection-surjectivity proof used by realization.
local instance : IsLocallySurjective sol.proj := sol.proj_locallySurjective

/-- Quasi-coherence follows from the specified kernel iso to the pulled conormal. -/
instance solutionKernel_quasicoherent :
    (kernelModule sol.proj sol.proj_squareZero).IsQuasicoherent := sorry

theorem solution_over : sol.structureMap ≫ sol.proj =
    commInverseImageStructureSheafMap (f ≫ t) :=
  sol.commutes.trans baseProjection_comp

/-- Full geometric realization data, including projection and base-algebra compatibility. -/
structure RealizationData where
  space : AlgebraicSpace S
  i : X ⟶ space
  over : space ⟶ Y'
  comparison : commInverseImageStructureSheaf i ⟶ sol.middle
  realizes : IsRealization (f ≫ t) sol.middle sol.proj sol.proj_squareZero sol.structureMap
    (solution_over L₀ sol) i over comparison

/-- Use the actual canonical realization theorem, with its complete specification. -/
theorem realizationData_nonempty : Nonempty (RealizationData L₀ sol) := by
  obtain ⟨Z, i, over, φ, h⟩ := exists_firstOrderThickening (f ≫ t)
    sol.middle sol.proj sol.proj_squareZero sol.structureMap (solution_over L₀ sol)
  exact ⟨⟨Z, i, over, φ, h⟩⟩

def realizationData : RealizationData L₀ sol := Classical.choice (realizationData_nonempty L₀ sol)

/-- The square-zero flatness criterion applies because sol induces the canonical base-kernel map. -/
theorem realization_flat (r : RealizationData L₀ sol) : Flat r.over := sorry

/-- The induced ideal map and reduction identify the closed fibre with X. -/
theorem realization_cartesian (r : RealizationData L₀ sol) : IsPullback f r.i t r.over := sorry

/-- Realize the specified extension as a flat lift, retaining the full 76.9.7 witness. -/
def fromSolution : FlatLift t f where
  space := (realizationData L₀ sol).space
  f' := (realizationData L₀ sol).over
  flat := realization_flat L₀ sol (realizationData L₀ sol)
  i := (realizationData L₀ sol).i
  isPullback := realization_cartesian L₀ sol (realizationData L₀ sol)

end AlgebraicGeometry.AlgebraicSpace.Thickening.FlatLift
