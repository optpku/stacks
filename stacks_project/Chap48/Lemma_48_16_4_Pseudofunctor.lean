module

public import ReasLib.AlgebraicGeometry.Scheme.Compactification.UpperShriek.Pseudofunctor

universe u

/- Lemma 48.16.4: the bounded-below upper-shriek construction is a contravariant
`Cat`-valued pseudofunctor on finite-type separated schemes over a Noetherian base. -/
#check (@AlgebraicGeometry.Scheme.UpperShriekAssignment.pseudofunctor :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsNoetherian S]
    (D : AlgebraicGeometry.Scheme.UpperShriekAssignment S),
    CategoryTheory.Pseudofunctor
      (CategoryTheory.LocallyDiscrete
        (AlgebraicGeometry.Scheme.FiniteTypeSeparatedOver S)ᵒᵖ)
      CategoryTheory.Cat)
