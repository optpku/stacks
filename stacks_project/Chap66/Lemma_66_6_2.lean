module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.AffineEtaleZariskiCover
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 66.6.2: let `S` be a scheme and `X` an algebraic space over `S`. There exists a
Zariski covering `X = ⋃ X_i` such that each algebraic space `X_i` has a surjective étale
covering by an affine scheme. We may in addition assume each `X_i` maps into an affine
open of `S`. -/
@[stacks 03FY] #check (AlgebraicGeometry.AlgebraicSpace.exists_affineEtaleZariskiCover :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} (X : AlgebraicGeometry.AlgebraicSpace S),
    Nonempty (AlgebraicGeometry.AlgebraicSpace.AffineEtaleZariskiCover.{u} X))
