module

public import ReasLib.AlgebraicGeometry.Scheme.GenericPoints.Dimension
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 28.10.4: a point `x` of a scheme `X` is a generic point of an irreducible component of
`X` if and only if the local ring `X.presheaf.stalk x` has Krull dimension `0`. -/
@[stacks 0BA9] #check
  (AlgebraicGeometry.Scheme.mem_genericPoints_iff_ringKrullDim_stalk_eq_zero :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} (x : X),
      x ∈ genericPoints X ↔ ringKrullDim (X.presheaf.stalk x) = 0)
