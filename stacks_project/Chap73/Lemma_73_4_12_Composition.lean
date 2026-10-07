module

public import stacks_project.Chap73.Lemma_73_4_10_Big

/-!
# Composition of big étale morphisms of topoi

This leaf owns the composition law for the bundled big étale morphism of topoi
attached to a pair of composable morphisms of algebraic spaces.
-/

@[expose] public section

open CategoryTheory
open scoped MorphismOfTopoiIn

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Etale.Big

/-- Big étale morphisms of topoi compose along composition of morphisms of
algebraic spaces. -/
theorem morphismOfTopoi_comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    MorphismOfTopoiIn.comp (morphismOfTopoi g) (morphismOfTopoi f) =
      morphismOfTopoi (f ≫ g) := sorry

end AlgebraicGeometry.AlgebraicSpace.Etale.Big
