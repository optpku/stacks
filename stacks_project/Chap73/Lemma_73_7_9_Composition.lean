/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap73.Lemma_73_7_8_Big

/-!
# Composition of big fppf morphisms of topoi

This leaf owns the composition law for the bundled big fppf morphism of topoi
attached to a pair of composable morphisms of algebraic spaces.
-/

@[expose] public section

open CategoryTheory
open scoped MorphismOfTopoiIn

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Fppf.Big

/-- Big fppf morphisms of topoi compose along composition of morphisms of
algebraic spaces. -/
theorem morphismOfTopoi_comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    MorphismOfTopoiIn.comp (morphismOfTopoi g) (morphismOfTopoi f) =
      morphismOfTopoi (f ≫ g) := sorry

end AlgebraicGeometry.AlgebraicSpace.Fppf.Big
