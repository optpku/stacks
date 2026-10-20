/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.GradedObject.ShiftedHom
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe v u

section

variable (𝒜 : Type u) [Category.{v} 𝒜] [Preadditive 𝒜]

/- Example 22.25.5 (Graded category of graded objects): applying the shifted-Hom category
construction to `GradedObject ℤ 𝒜` gives the graded category whose degree-`n` morphisms are
`ShiftedHom X Y n`. -/
@[stacks 09MM] #check
  (GradedObject.ShiftedHom.grading 𝒜 :
    GradedCategory ℤ (ShiftedHomCategory (GradedObject ℤ 𝒜)) ℤ)

/- The canonical grading is available to downstream code by typeclass inference. -/
#check (inferInstance :
  GradedCategory ℤ (ShiftedHomCategory (GradedObject ℤ 𝒜)) ℤ)

end

/- The total morphism object is the direct sum of its shifted-Hom pieces. -/
#check @ShiftedHomCategory.homSpace

/- Homogeneous composition adds the two degrees. -/
#check @ShiftedHomCategory.compHomDegree

/- The degree-zero piece recovers the ordinary morphisms of the original category. -/
#check @ShiftedHomCategory.degreeZeroHomEquiv
