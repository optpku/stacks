module

public import ReasLib.AlgebraicGeometry.Scheme.Germ.Morphism.EtaleLocal

@[expose] public section

universe u

/- Compatibility check for the source-and-target étale-locality predicate on germ morphisms. -/
#check (AlgebraicGeometry.Scheme.Germ.MorphismProperty.IsEtaleLocal :
  CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.Germ.{u} → Prop)
