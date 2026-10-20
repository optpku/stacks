/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.IsomorphismClasses
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.SpacesTopos
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Relocalization
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.BigTopos

/-!
# Mixed small-to-big étale base change for algebraic spaces

A cartesian square of algebraic spaces induces the mixed identification
between big étale direct image and spaces-étale direct image after
relocalization.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open scoped MorphismOfTopoiIn

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Etale.SpacesToBig

variable {S : Scheme.{u}} {X X' Y Y' : AlgebraicSpace S}

/-- In a cartesian square of algebraic spaces, big étale direct image followed by
spaces-étale-to-big inverse image is isomorphic to spaces-étale-to-big inverse
image followed by spaces-étale direct image. -/
theorem pushforwardBaseChange_isomorphic
    (f : Y ⟶ X) (g : X' ⟶ X) (f' : Y' ⟶ X') (g' : Y' ⟶ Y)
    (sq : IsPullback g' f' f g) :
    IsIsomorphic
      ((Etale.Big.morphismOfTopoi f) _* ⋙
        (morphismOfTopoi g)⁻¹)
      ((morphismOfTopoi g')⁻¹ ⋙
        (spacesEtaleMorphismOfTopoi f') _*) := sorry

end AlgebraicGeometry.AlgebraicSpace.Etale.SpacesToBig
