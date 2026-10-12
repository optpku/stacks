/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Descent
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u v

/- Definition 35.2.1: descent data for quasi-coherent sheaves with respect to a family of
scheme morphisms, together with their compatible componentwise morphisms. -/
@[stacks 023B] #check
  (@AlgebraicGeometry.Scheme.QCoh.DescentData :
    {I : Type v} → {S : Scheme.{u}} →
      (X : I → Scheme.{u}) → ((i : I) → X i ⟶ S) →
        Type (max (u + 1) v))

#check @AlgebraicGeometry.Scheme.QCoh.DescentData.of
#check @AlgebraicGeometry.Scheme.QCoh.DescentData.homExt
#check @AlgebraicGeometry.Scheme.QCoh.DescentData.Chosen
#check @AlgebraicGeometry.Scheme.QCoh.DescentData.Chosen.transitionIso
#check @AlgebraicGeometry.Scheme.QCoh.DescentData.Chosen.cocycle
#check @AlgebraicGeometry.Scheme.QCoh.DescentData.Chosen.hom_compatibility
#check @AlgebraicGeometry.Scheme.QCoh.DescentData.Chosen.equivalence
