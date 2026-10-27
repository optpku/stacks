/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening.FlatLift.Conormal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening.SquareZeroRealization
public import ReasLib.AlgebraicGeometry.RingedSite.FirstOrderThickening.Solution
public section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.SquareZeroExtension
open SheafOfModules.RingedSite
noncomputable section
universe u
namespace AlgebraicGeometry.AlgebraicSpace.Thickening.FlatLift
variable {S : Scheme.{u}} {Y Y' X : AlgebraicSpace S}
variable {t : Y ⟶ Y'} [IsFirstOrderThickening t] {f : X ⟶ Y} [Flat f]
/-- The square-zero étale algebra `i⁻¹ 𝒪_{X'}` of a flat lift. -/
@[expose] def liftAlgebra (L : FlatLift t f) :
    Sheaf (smallEtaleTopology X) CommRingCat.{u} :=
  commInverseImageStructureSheaf L.i

/-- Projection `i⁻¹ 𝒪_{X'} ⟶ 𝒪_X` of a flat lift. -/
@[expose] def liftAlgebraProj (L : FlatLift t f) :
    liftAlgebra L ⟶ commStructureSheaf X :=
  commInverseImageStructureSheafMap L.i

/-- The `𝒪_{Y'}`-algebra structure on `i⁻¹ 𝒪_{X'}`, transported along the cartesian
square `L.i ≫ L.f' = f ≫ t`. -/
@[expose] def liftAlgebraOver (L : FlatLift t f) :
    commInverseImageStructureSheaf (f ≫ t) ⟶ liftAlgebra L :=
  (commInverseImageCongr L.isPullback.w).hom ≫
    algebraMap L.i (L.i ≫ L.f') L.f' rfl

/-- `liftAlgebraOver` is `algebraMap` of `L.i` after identifying `f ≫ t` with
`L.i ≫ L.f'`. -/
theorem liftAlgebraOver_spec (L : FlatLift t f) :
    liftAlgebraOver L =
      (commInverseImageCongr L.isPullback.w).hom ≫
        algebraMap L.i (L.i ≫ L.f') L.f' rfl :=
  sorry

/-- The projection `i⁻¹ 𝒪_{X'} ⟶ 𝒪_X` of a flat lift is locally surjective. -/
theorem liftAlgebraProj_locallySurjective (L : FlatLift t f) :
    Sheaf.IsLocallySurjective (liftAlgebraProj L) := sorry

/-- The projection `i⁻¹ 𝒪_{X'} ⟶ 𝒪_X` of a flat lift is a square-zero extension. -/
theorem liftAlgebra_squareZero (L : FlatLift t f) :
    KernelIdeal.IsSquareZero (liftAlgebraProj L) := sorry

/-- Inverse image of the thickening map `t^♯` along `f`. -/
def inverseImageThickeningMap :
    commInverseImageStructureSheaf (f ≫ t) ⟶ commInverseImageStructureSheaf f :=
  (commSheafInverseImageCompIso f t (commStructureSheaf Y')).inv ≫
    commSheafInverseImageMap f (commInverseImageStructureSheafMap t)


end AlgebraicGeometry.AlgebraicSpace.Thickening.FlatLift

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Hom.Deformation
open AlgebraicGeometry.AlgebraicSpace.SquareZeroExtension
open SheafOfModules.RingedSite
noncomputable section
namespace AlgebraicGeometry.AlgebraicSpace.Thickening.FlatLift.SmallKernel
variable {S : Scheme.{u}} {Y Y' X : AlgebraicSpace S}
variable {t : Y ⟶ Y'} [IsFirstOrderThickening t] {f : X ⟶ Y} [Flat f]

/-- The additive sheaf underlying the unit module of an étale ring sheaf. -/
private abbrev unitAdd (A : Sheaf (smallEtaleTopology X) CommRingCat.{u}) :=
  (SheafOfModules.toSheaf (ringSheaf.{u + 1, u, u} (smallEtaleTopology X) A)).obj
    (unitModule (smallEtaleTopology X) A)

/-- The structure module has the same underlying sections as the ring. -/
private def unitUnderlyingTypeIso (A : Sheaf (smallEtaleTopology X) CommRingCat.{u}) :
    (EtaleAdditive.ForgetComparison.forgetAdd X).obj (unitAdd A) ≅
      (sheafCompose (smallEtaleTopology X) (forget CommRingCat.{u})).obj A where
  hom := { hom := { app := fun _ ↦ 𝟙 _, naturality := sorry } }
  inv := { hom := { app := fun _ ↦ 𝟙 _, naturality := sorry } }
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The small/spaces comparison is the composite of the existing adjunction mates,
ring-forget comparison, and the fixed underlying structure-module identification. -/
private def restrictionTypeComparison (L : FlatLift t f) :
    (EtaleAdditive.ForgetComparison.forgetAdd X).obj ((EtaleAdditive.restriction X).obj
      ((forgetSpacesRing X).obj (closedStructureSheaf L.i))) ⟶
    (EtaleAdditive.ForgetComparison.forgetAdd X).obj (unitAdd (liftAlgebra L)) :=
  restrictInverseImageTypeHom L.i ≫
    inv (inverseImageForgetAddHom L.i
      ((sheafCompose (smallEtaleTopology L.space) (forget₂ RingCat AddCommGrpCat.{u})).obj
        (structureSheaf L.space))) ≫
    (morphismOfTopoi L.i).ringInverseImageForgetIso.inv.app (structureSheaf L.space) ≫
    eqToHom (congrArg
      (fun R : Sheaf (smallEtaleTopology X) RingCat.{u} ↦
        (sheafCompose (smallEtaleTopology X) (forget RingCat.{u})).obj R)
      (commInverseImageStructureSheaf_forget L.i).symm) ≫
    (unitUnderlyingTypeIso (liftAlgebra L)).inv

/-- The comparison of inverse-image rings preserves their additive structure. -/
private theorem restrictionTypeComparison_add (L : FlatLift t f) :
    typeHomIsAdditive (restrictionTypeComparison L) := sorry

/-- The additive comparison from restricted closed structure sheaves to the inverse-image algebra. -/
private def restrictionAddComparison (L : FlatLift t f) :
    (EtaleAdditive.restriction X).obj ((forgetSpacesRing X).obj (closedStructureSheaf L.i)) ⟶
    unitAdd (liftAlgebra L) :=
  EtaleAdditive.ForgetComparison.homOfUnderlying (restrictionTypeComparison L)
    (restrictionTypeComparison_add L)

/-- The specified geometric ideal inclusion in the small-site extension algebra. -/
def inclusion (L : FlatLift t f) :
    (SheafOfModules.toSheaf (structureSheaf X)).obj (pulledConormal t f) ⟶
      (SheafOfModules.toSheaf (ringSheaf.{u + 1, u, u}
        (smallEtaleTopology X) (liftAlgebra L))).obj
      (unitModule (smallEtaleTopology X) (liftAlgebra L)) :=
  CanonicalKernel.inclusion L ≫ restrictionAddComparison L

/-- The geometric ideal inclusion is annihilated by reduction to the closed fibre. -/
theorem inclusion_comp_projection (L : FlatLift t f) :
    inclusion L ≫
      (SheafOfModules.toSheaf (ringSheaf.{u + 1, u, u} (smallEtaleTopology X) (liftAlgebra L))).map
        (KernelIdeal.map (liftAlgebraProj L)) = 0 := sorry

/-- The additive comparison is kernel.lift, followed by the specified target-module descent. -/
def kernelComparisonAdd (L : FlatLift t f) :
    (SheafOfModules.toSheaf (structureSheaf X)).obj (pulledConormal t f) ⟶
      (SheafOfModules.toSheaf (structureSheaf X)).obj
        (@kernelModule _ _ _ (liftAlgebraProj L) (liftAlgebraProj_locallySurjective L)
      (liftAlgebra_squareZero L)) :=
  KernelIdeal.additiveLift (liftAlgebraProj L) (inclusion L) (inclusion_comp_projection L) ≫
    (@kernelModuleForgetIso _ _ _ (liftAlgebraProj L) (liftAlgebraProj_locallySurjective L)
      (liftAlgebra_squareZero L)).inv

/-- The module comparison has the above fixed section function. -/
def kernelComparison (L : FlatLift t f) :
    pulledConormal t f ⟶ @kernelModule _ _ _ (liftAlgebraProj L) (liftAlgebraProj_locallySurjective L)
      (liftAlgebra_squareZero L) where
  val := PresheafOfModules.homMk
    ((sheafToPresheaf (smallEtaleTopology X) AddCommGrpCat.{u}).map (kernelComparisonAdd L))
    (fun _ _ _ ↦ sorry)

/-- The cartesian, flat first-order square identifies its two kernel modules by this map. -/
theorem kernelComparison_isIso (L : FlatLift t f) : IsIso (kernelComparison L) := sorry

/-- The inverse of the canonical conormal-to-kernel module comparison. -/
def kernelIso (L : FlatLift t f) :
    @kernelModule _ _ _ (liftAlgebraProj L) (liftAlgebraProj_locallySurjective L)
      (liftAlgebra_squareZero L) ≅ pulledConormal t f :=
  (@asIso _ _ _ _ (kernelComparison L) (kernelComparison_isIso L)).symm

/-- The inverse kernel comparison is the defining module map. -/
private theorem kernelIsoInvEq (L : FlatLift t f) :
    (kernelIso L).inv = kernelComparison L := rfl

/-- The inverse kernel isomorphism is the canonical kernel comparison. -/
@[simp] theorem kernelIso_inv (L : FlatLift t f) :
    (kernelIso L).inv = kernelComparison L := kernelIsoInvEq L
end AlgebraicGeometry.AlgebraicSpace.Thickening.FlatLift.SmallKernel

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace AlgebraicGeometry.AlgebraicSpace.SquareZeroExtension
open SheafOfModules.RingedSite
noncomputable section
namespace AlgebraicGeometry.AlgebraicSpace.Thickening.FlatLift
variable {S : Scheme.{u}} {Y Y' X : AlgebraicSpace S}
variable {t : Y ⟶ Y'} [IsFirstOrderThickening t] {f : X ⟶ Y} [Flat f]

/-- Inverse image of a first-order thickening map is locally surjective. -/
instance baseProjection_surjective : IsLocallySurjective (inverseImageThickeningMap (t := t) (f := f)) := sorry

/-- Inverse image of a first-order thickening map has square-zero kernel. -/
theorem baseProjection_squareZero : KernelIdeal.IsSquareZero
    (inverseImageThickeningMap (t := t) (f := f)) := sorry

/-- The inverse-image thickening map followed by reduction is the composite structure map. -/
theorem baseProjection_comp : inverseImageThickeningMap (t := t) (f := f) ≫
    commInverseImageStructureSheafMap f = commInverseImageStructureSheafMap (f ≫ t) := sorry

/-- The algebra structure of a flat lift commutes with reduction to the closed fibre. -/
theorem liftAlgebra_commutes (L : FlatLift t f) :
    liftAlgebraOver L ≫ liftAlgebraProj L =
      inverseImageThickeningMap (t := t) (f := f) ≫ commInverseImageStructureSheafMap f := sorry

/-- The actual induced map on base kernels, expressed in the geometrically fixed coefficient module. -/
def equationMap (L : FlatLift t f) :=
  FirstOrderThickening.kernelMapOf.{u + 1, u, u}
    (inverseImageThickeningMap (t := t) (f := f)) (baseProjection_squareZero (t := t) (f := f))
    (commInverseImageStructureSheafMap f) (liftAlgebraProj L) (liftAlgebra_squareZero L)
    (@KernelIdeal.quotientComparison_isIso _ _ _ _ _ _ _ (liftAlgebraProj L) _
      (liftAlgebraProj_locallySurjective L)) (liftAlgebraOver L)
    (liftAlgebra_commutes L) ≫
      (restrictionAlong (commInverseImageStructureSheafMap f)).map (SmallKernel.kernelIso L).hom

/-- All cartesian lifts induce the same base-kernel map: their kernel identifications
were constructed from the same geometric pullback inclusion, not chosen independently. -/
theorem equationMap_eq (L₁ L₂ : FlatLift t f) : equationMap L₁ = equationMap L₂ := sorry

/-- Square-zero extension solutions with the coefficient equation induced by a fixed flat lift. -/
abbrev LiftSolution (L : FlatLift t f) :=
  FirstOrderThickening.Solution.{u + 1, u, u}
    (inverseImageThickeningMap (t := t) (f := f)) (baseProjection_squareZero (t := t) (f := f))
    (commInverseImageStructureSheafMap f) (pulledConormal t f) (equationMap L)

/-- Rebundle a second actual flat lift as a solution of the fixed basepoint equation. -/
def toSolution (L₀ L : FlatLift t f) : LiftSolution L₀ where
  middle := liftAlgebra L
  proj := liftAlgebraProj L
  structureMap := liftAlgebraOver L
  proj_locallySurjective := liftAlgebraProj_locallySurjective L
  proj_squareZero := liftAlgebra_squareZero L
  proj_quotient_isIso := @KernelIdeal.quotientComparison_isIso _ _ _ _ _ _ _ (liftAlgebraProj L) _
      (liftAlgebraProj_locallySurjective L)
  commutes := liftAlgebra_commutes L
  kernelIso := SmallKernel.kernelIso L
  induces_c := equationMap_eq L L₀

/-- The displayed construction has the specified component formula. -/
private theorem toSolution_middleEq (L₀ L : FlatLift t f) :
    (toSolution L₀ L).middle = liftAlgebra L := rfl

/-- The middle algebra is the real inverse image of the ambient structure sheaf. -/
@[simp] theorem toSolution_middle (L₀ L : FlatLift t f) :
    (toSolution L₀ L).middle = liftAlgebra L := toSolution_middleEq L₀ L

variable (L₀ : FlatLift t f) (sol : LiftSolution L₀)

/-- Quasi-coherence follows from the specified kernel iso to the pulled conormal. -/
theorem solutionKernel_quasicoherent :
    (@kernelModule _ _ _ sol.proj sol.proj_locallySurjective sol.proj_squareZero).IsQuasicoherent := sorry

/-- A solution algebra reduces to the structure map of the composite base morphism. -/
theorem solution_over : sol.structureMap ≫ sol.proj =
    commInverseImageStructureSheafMap (f ≫ t) :=
  sol.commutes.trans baseProjection_comp

/-- Full geometric realization data, including projection and base-algebra compatibility. -/
structure RealizationData where
  /-- The ambient algebraic space of the realization. -/
  space : AlgebraicSpace S
  /-- The closed-fibre embedding into the realization. -/
  i : X ⟶ space
  /-- The structure morphism to the thickened base. -/
  over : space ⟶ Y'
  /-- The comparison from the realized structure sheaf to the solution algebra. -/
  comparison : commInverseImageStructureSheaf i ⟶ sol.middle
  /-- The comparison is an algebra isomorphism compatible with reduction and the base. -/
  realizes : @IsRealization _ _ _ (f ≫ t) sol.middle sol.proj sol.proj_locallySurjective sol.proj_squareZero sol.structureMap
    (solution_over L₀ sol) space i over comparison

/-- Use the actual canonical realization theorem, with its complete specification. -/
theorem realizationData_nonempty : Nonempty (RealizationData L₀ sol) := by
  obtain ⟨Z, i, over, φ, h⟩ := @exists_firstOrderThickening _ _ _ (f ≫ t) sol.middle sol.proj
    sol.proj_locallySurjective sol.proj_squareZero (solutionKernel_quasicoherent L₀ sol)
    sol.structureMap (solution_over L₀ sol)
  exact ⟨⟨Z, i, over, φ, h⟩⟩

/-- A geometric realization of the specified square-zero extension algebra. -/
def realizationData : RealizationData L₀ sol := Classical.choice (realizationData_nonempty L₀ sol)

/-- The selected realization is a first-order thickening over the base, with an algebra
isomorphism compatible with reduction and the base-algebra map. -/
theorem realizationData_spec :
    IsFirstOrderThickening (realizationData L₀ sol).i ∧
      ∃ h_over : (realizationData L₀ sol).i ≫ (realizationData L₀ sol).over = f ≫ t,
        IsIso (realizationData L₀ sol).comparison ∧
        (realizationData L₀ sol).comparison ≫ sol.proj =
          commInverseImageStructureSheafMap (realizationData L₀ sol).i ∧
        sol.structureMap = algebraMap (realizationData L₀ sol).i (f ≫ t)
          (realizationData L₀ sol).over h_over ≫ (realizationData L₀ sol).comparison :=
  ⟨(@IsRealization.isFirstOrder _ _ _ (f ≫ t) sol.middle sol.proj
      sol.proj_locallySurjective sol.proj_squareZero sol.structureMap
      (solution_over L₀ sol) _ _ _ _ (realizationData L₀ sol).realizes),
    (@IsRealization.overBase _ _ _ (f ≫ t) sol.middle sol.proj
      sol.proj_locallySurjective sol.proj_squareZero sol.structureMap
      (solution_over L₀ sol) _ _ _ _ (realizationData L₀ sol).realizes),
    (@IsRealization.isIso _ _ _ (f ≫ t) sol.middle sol.proj
      sol.proj_locallySurjective sol.proj_squareZero sol.structureMap
      (solution_over L₀ sol) _ _ _ _ (realizationData L₀ sol).realizes),
    (@IsRealization.compatibleSurjection _ _ _ (f ≫ t) sol.middle sol.proj
      sol.proj_locallySurjective sol.proj_squareZero sol.structureMap
      (solution_over L₀ sol) _ _ _ _ (realizationData L₀ sol).realizes),
    (@IsRealization.compatibleAlgebra _ _ _ (f ≫ t) sol.middle sol.proj
      sol.proj_locallySurjective sol.proj_squareZero sol.structureMap
      (solution_over L₀ sol) _ _ _ _ (realizationData L₀ sol).realizes)⟩

/-- The square-zero flatness criterion applies because sol induces the canonical base-kernel map. -/
theorem realization_flat (r : RealizationData L₀ sol) : Flat r.over := sorry

/-- The induced ideal map and reduction identify the closed fibre with X. -/
theorem realization_cartesian (r : RealizationData L₀ sol) : IsPullback f r.i t r.over := sorry

/-- Realize the specified extension as a flat lift, retaining its algebra comparison. -/
@[expose] def fromSolution : FlatLift t f where
  space := (realizationData L₀ sol).space
  f' := (realizationData L₀ sol).over
  flat := realization_flat L₀ sol (realizationData L₀ sol)
  i := (realizationData L₀ sol).i
  isPullback := realization_cartesian L₀ sol (realizationData L₀ sol)

end AlgebraicGeometry.AlgebraicSpace.Thickening.FlatLift
