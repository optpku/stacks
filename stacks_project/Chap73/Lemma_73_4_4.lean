module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.AlgebraicSpace.Cover.Smooth.EtaleRefinement

/-!
# Étale refinements of smooth coverings of algebraic spaces

Every smooth covering family of an algebraic space admits an étale covering
that refines it.
-/

open CategoryTheory
open CategoryTheory.SemiRepresentableFamily.Over
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u v

/- Lemma 73.4.4: let `S` be a scheme and let `X` be an algebraic space over
`S`. If `{X_i ⟶ X}` is a smooth covering of `X`, then there exists an étale
covering `{U_j ⟶ X}` of `X` which refines `{X_i ⟶ X}`. -/
@[stacks 0CFV] #check
  (AlgebraicGeometry.AlgebraicSpace.SmoothCovering.exists_etaleRefinement :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
      {ι : Type v} {family : ι → Over X}, SmoothCovering family →
      ∃ 𝒱 : (@etalePrecoverage S).ZeroHypercover.{u} X,
        Refines (ofArrows 𝒱.X 𝒱.f)
          (ofArrows (fun i ↦ (family i).left) (fun i ↦ (family i).hom)))
