module

public import stacks_project.Chap66.Lemma_66_16_6_Postcomp
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

/- Lemma 67.39.11: let `S` be a scheme, and let `X`, `Y` be algebraic spaces étale
over an algebraic space `Z`. Any morphism `X ⟶ Y` over `Z` is étale. -/
@[stacks 05W3] #check
  (AlgebraicGeometry.AlgebraicSpace.Etale.of_comp :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) {Z : AlgebraicSpace S}
      (g : Y ⟶ Z) [AlgebraicSpace.Etale (f ≫ g)] [AlgebraicSpace.Etale g],
      AlgebraicSpace.Etale f)
