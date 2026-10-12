/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Germ.Morphism.EtaleLocal

@[expose] public section

universe u

/- Compatibility check for the source-and-target étale-locality predicate on germ morphisms. -/
#check (AlgebraicGeometry.Scheme.Germ.MorphismProperty.IsEtaleLocal :
  CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.Germ.{u} → Prop)
