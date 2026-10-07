module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Envelope

universe u

/- The compatibility module exposes the shared envelope predicate at its complete type. -/
#check
  (AlgebraicGeometry.IsEnvelope : {Y X : AlgebraicGeometry.Scheme.{u}} → (Y ⟶ X) → Prop)
