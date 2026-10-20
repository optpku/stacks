/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Polynomial
public import stacks_project.Chap66.Definition_66_18_1_Site

/-!
# Polynomial affine-space objects in the small étale site

The étale scheme of a polynomial affine-space object defines an object of the small
étale site of the algebraic space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Polynomial

variable {R : CommRingCat.{u}} {X : AlgebraicSpace (Spec R)}

namespace Object

/-- The image of the object in the small étale site of `X`. -/
def asSite (obj : Object R X) : smallEtaleSite X :=
  MorphismProperty.CostructuredArrow.mk ⊤ obj.toSpace obj.etale

end Object

end AlgebraicGeometry.AlgebraicSpace.Polynomial
