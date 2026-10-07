module

public import stacks_project.Chap66.Lemma_66_4_4_Surjective
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

/- Lemma 66.4.4: let `S` be a scheme. Let `X` be an algebraic space over `S`. Let
`f : T ⟶ X` be a morphism from a scheme to `X`. Then `f` is surjective according to
Spaces, Definition 65.5.1 if and only if `|f| : |T| ⟶ |X|` is surjective. -/
@[stacks 03H5] #check
  (ofOver_presheaf_surjective_iff :
    ∀ {S : Scheme.{u}} {T : Over S} {X : AlgebraicSpace S} (f : ofOver T ⟶ X),
      (MorphismProperty.over (@AlgebraicGeometry.Surjective)).presheaf f ↔
        Function.Surjective (Points.map f))
