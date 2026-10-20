/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ChowMotive
public import ReasLib.CategoryTheory.Idempotents.Karoubi.Monoidal
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Point

@[expose] public section

open CategoryTheory CategoryTheory.Idempotents
open scoped CategoryTheory.MonoidalCategory

universe w v u

variable (k : Type u) [Field k]
variable (GradedCorrespondence : Type u → Type v)
variable [Category.{w} (GradedCorrespondence k)]
variable [MonoidalCategory (GradedCorrespondence k)]
variable [SymmetricCategory (GradedCorrespondence k)]
variable (gradedObject : AlgebraicGeometry.SchemeOverField k → ℤ → GradedCorrespondence k)

namespace ChowMotive

/-- The tensor unit of the category of Chow motives is the identity formal image of the
ambient graded-correspondence unit, hence of the degree-zero motive of the spectrum of `k`
whenever that unit is identified with `gradedObject (SchemeOverField.point k) 0`. -/
theorem tensorUnit_eq
    (h_unit : 𝟙_ (GradedCorrespondence k) =
      gradedObject (AlgebraicGeometry.SchemeOverField.point k) 0) :
    𝟙_ (ChowMotive k GradedCorrespondence) =
      (gradedObject (AlgebraicGeometry.SchemeOverField.point k) 0 :
        Karoubi (GradedCorrespondence k)) := sorry

end ChowMotive
