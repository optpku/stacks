module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.Classifying

/-! # Classification of families of curves over algebraic spaces -/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 109.3.1: for every morphism of algebraic spaces T ⟶ B, relative morphisms
into B-Curves identify with absolute morphisms into Curves and classify flat, proper,
finitely presented families over T of relative dimension at most one. -/
@[stacks 0DMK] #check
  (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.classifying_equivalences :
    ∀ {S : Scheme.{u}} {T B : AlgebraicSpace S} (b : T ⟶ B),
      (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.forgetBase b).IsEquivalence ∧
      (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.classifying T).IsEquivalence ∧
      (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.classifyingOver b).IsEquivalence)
