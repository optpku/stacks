module

public import ReasLib.AlgebraicGeometry.Scheme.EtaleEquivalenceRelation

@[expose] public section

universe u

#check (AlgebraicGeometry.Scheme.PreRelation.IsEtaleEquivalenceRelation :
  {S : AlgebraicGeometry.Scheme.{u}} → {U : CategoryTheory.Over S} →
    AlgebraicGeometry.Scheme.PreRelation U → Prop)
