/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap74.Definition_74_3_1_Pseudofunctor
public import stacks_project.Chap74.Definition_74_3_1_DescentData
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u v

/- Definition 74.3.1: descent data for quasi-coherent sheaves with respect to a family of
morphisms of algebraic spaces over a scheme `S` with fixed target, together with their
compatible componentwise morphisms. -/
@[stacks 04W3] #check
  (@AlgebraicGeometry.AlgebraicSpace.QCoh.DescentData :
    {I : Type v} → {S : Scheme.{u}} → {X : AlgebraicSpace S} →
      (Xᵢ : I → AlgebraicSpace S) → ((i : I) → Xᵢ i ⟶ X) →
        Type (max (u + 1) v))

#check @AlgebraicGeometry.AlgebraicSpace.QCoh.DescentData.of
#check @AlgebraicGeometry.AlgebraicSpace.QCoh.DescentData.homExt
#check @AlgebraicGeometry.AlgebraicSpace.QCoh.DescentData.Chosen
#check @AlgebraicGeometry.AlgebraicSpace.QCoh.DescentData.Chosen.transitionIso
#check @AlgebraicGeometry.AlgebraicSpace.QCoh.DescentData.Chosen.cocycle
#check @AlgebraicGeometry.AlgebraicSpace.QCoh.DescentData.Chosen.hom_compatibility
#check @AlgebraicGeometry.AlgebraicSpace.QCoh.DescentData.Chosen.equivalence
