module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.H.ChosenPresentation.Affine
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u v

/- Definition 38.34.13 (1): the big h site over `S` is the slice of a chosen
big h site by `S`, equipped with the induced slice topology. -/
@[stacks 0EU1] #check
  (AlgebraicGeometry.ChosenBigHSite.bigTopology :
    (X : AlgebraicGeometry.ChosenBigHSite.{u, v}) →
      (S : X.carrier) → GrothendieckTopology (Over S))

/- Definition 38.34.13 (2): the big affine h site over `S` is the affine full
subcategory of the big h slice, with coverings that cover in the ambient
slice and are represented by finite affine h covering families. -/
@[stacks 0EU1] #check
  (AlgebraicGeometry.ChosenBigHSite.bigAffineTopology :
    (X : AlgebraicGeometry.ChosenBigHSite.{u, v}) →
      (S : X.carrier) →
        GrothendieckTopology
          (AlgebraicGeometry.ChosenBigSite.affineSite X S))
