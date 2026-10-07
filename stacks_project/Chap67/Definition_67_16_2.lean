module

public import stacks_project.Chap67.Lemma_67_16_6_SchemeTheoreticImage
public import stacks_project.Chap67.Lemma_67_16_1
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Definition 67.16.2: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. The scheme-theoretic image of `f` is the smallest
closed subspace `Z ⊂ Y` through which `f` factors, as supplied by Lemma 67.16.1. -/
@[stacks 082Y] #check AlgebraicGeometry.AlgebraicSpace.IsSchemeTheoreticImage

/- A least closed-subspace factorization of `f` is a scheme-theoretic image
factorization, recovering the smallest-closed-subspace wording. -/
@[stacks 082Y] #check
  (@AlgebraicGeometry.AlgebraicSpace.IsSchemeTheoreticImage.of_isLeast_closedSubspace :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      (Z : AlgebraicSpace.ClosedSubspace Y) (toImage : X ⟶ Z.X),
      toImage ≫ Z.ι = f →
        (∀ Z' : AlgebraicSpace.ClosedSubspace Y,
            (∃ toZ' : X ⟶ Z'.X, toZ' ≫ Z'.ι = f) →
              ∃ k : Z.X ⟶ Z'.X, k ≫ Z'.ι = Z.ι) →
          AlgebraicGeometry.AlgebraicSpace.IsSchemeTheoreticImage f toImage Z.ι)
