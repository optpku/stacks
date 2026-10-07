module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Coordinate
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Twist
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.TopSections

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveSpace

/-- The global section of `𝒪(1)` on standard projective space defined by the homogeneous
coordinate `T_i`. -/
noncomputable def coordinateTwistSection
    (R : Type u) [CommRing R] (n : ℕ) (i : Fin (n + 1)) :
    (twistingSheaf R n 1).sections :=
  RingedSpace.sectionFromTop (twistingSheaf R n 1)
    (Proj.AssociatedModule.degreeZeroToGlobalSections (grading R n)
      (GradedModule.shiftGrading
        (DirectSum.Decomposition.natToIntGrading (grading R n)) (1 : ℤ))
      ⟨coordinate (R := R) n i, coordinate_mem_grading_one (R := R) n i⟩)

/-- The value on the top open of `coordinateTwistSection` is the canonical twist section of
the corresponding homogeneous coordinate. -/
theorem coordinateTwistSection_apply_top
    (R : Type u) [CommRing R] (n : ℕ) (i : Fin (n + 1)) :
    (coordinateTwistSection R n i).1 (Opposite.op ⊤) =
      Proj.AssociatedModule.degreeZeroToGlobalSections (grading R n)
        (GradedModule.shiftGrading
          (DirectSum.Decomposition.natToIntGrading (grading R n)) (1 : ℤ))
        ⟨coordinate (R := R) n i, coordinate_mem_grading_one (R := R) n i⟩ := sorry

end AlgebraicGeometry.ProjectiveSpace
