module

public import stacks_project.Chap37.Lemma_37_66_2_IndQuasiAffine
import StacksCheckRecall

universe u

/- Definition 37.66.1 (1): A scheme is ind-quasi-affine when every quasi-compact
open subscheme is quasi-affine. -/
@[stacks 0AP6] #check
  (AlgebraicGeometry.Scheme.IsIndQuasiAffine : AlgebraicGeometry.Scheme.{u} → Prop)

/- Definition 37.66.1 (2): A morphism is ind-quasi-affine when the inverse image
of every affine target open is ind-quasi-affine. -/
@[stacks 0AP6] #check
  (@AlgebraicGeometry.IndQuasiAffineHom :
    CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})
