/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.EtaleLocal

universe u

#check (AlgebraicGeometry.IsEtaleLocalAtSourceAndTarget :
  CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u} → Prop)
