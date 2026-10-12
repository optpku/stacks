/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.IsomorphismClasses
public import stacks_project.Chap66.Lemma_66_18_8_Topos
public import stacks_project.Chap73.Lemma_73_4_7_Relocalization
public import stacks_project.Chap73.Lemma_73_4_10_Big

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
