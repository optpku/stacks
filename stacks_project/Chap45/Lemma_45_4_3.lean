/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ChowMotive.Monoidal
import StacksCheckRecall

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

/- Lemma 45.4.3
The category of Chow motives is symmetric monoidal with unit the identity formal
image of `(Spec(k), 1, 0)`. -/
@[stacks 0FGC]
#check (CategoryTheory.Idempotents.Karoubi.instSymmetricCategory :
    ∀ {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C],
      SymmetricCategory (Karoubi C))

#check (ChowMotive.tensorUnit_eq k GradedCorrespondence gradedObject :
    𝟙_ (GradedCorrespondence k) =
        gradedObject (AlgebraicGeometry.SchemeOverField.point k) 0 →
      𝟙_ (ChowMotive k GradedCorrespondence) =
        (gradedObject (AlgebraicGeometry.SchemeOverField.point k) 0 :
          Karoubi (GradedCorrespondence k)))
