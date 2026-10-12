/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module
public import stacks_project.Chap91.Lemma_91_14_2_Lift
public import stacks_project.Chap76.Lemma_76_9_7_SquareZero
@[expose] public section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.SquareZeroExtension
open SheafOfModules.RingedSite
noncomputable section
universe u
namespace AlgebraicGeometry.AlgebraicSpace.Thickening.FlatLift
variable {S : Scheme.{u}} {Y Y' X : AlgebraicSpace S}
variable {t : Y ⟶ Y'} [IsFirstOrderThickening t] {f : X ⟶ Y} [Flat f]
/-- Rebundle a realized square-zero étale algebra as a flat lift, given the
algebraic-space carrier, ambient map, and cartesian square. -/
def ofSolution (X' : AlgebraicSpace S) (f' : X' ⟶ Y') [Flat f'] (i : X ⟶ X')
    (isPullback : IsPullback f i t f') : FlatLift t f :=
  of f' i isPullback

/-- The square-zero étale algebra `i⁻¹ 𝒪_{X'}` of a flat lift. -/
def liftAlgebra (L : FlatLift t f) :
    Sheaf (smallEtaleTopology X) CommRingCat.{u} :=
  commInverseImageStructureSheaf L.i

/-- Projection `i⁻¹ 𝒪_{X'} ⟶ 𝒪_X` of a flat lift. -/
def liftAlgebraProj (L : FlatLift t f) :
    liftAlgebra L ⟶ commStructureSheaf X :=
  commInverseImageStructureSheafMap L.i

/-- The `𝒪_{Y'}`-algebra structure on `i⁻¹ 𝒪_{X'}`, transported along the cartesian
square `L.i ≫ L.f' = f ≫ t`. -/
def liftAlgebraOver (L : FlatLift t f) :
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
instance instIsLocallySurjective_liftAlgebraProj (L : FlatLift t f) :
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
