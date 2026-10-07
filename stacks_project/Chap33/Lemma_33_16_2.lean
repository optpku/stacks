module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.TangentSpace.DottedArrow

@[expose] public section

open CategoryTheory

universe u

/- Lemma 33.16.2: The set of dotted arrows making the dual-number square at
`x` commute has a canonical `X.residueField x`-vector-space structure. -/
@[stacks 0B2B] #check
  (AlgebraicGeometry.Scheme.Hom.dottedTangentArrowModule :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S) (x : X),
      Module (X.residueField x)
        (AlgebraicGeometry.Scheme.Hom.DottedTangentArrow f x))
