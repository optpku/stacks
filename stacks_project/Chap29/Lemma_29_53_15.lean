module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Normalization.Nagata

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Lemma 29.53.15: let `f : X ⟶ S` be a finite-type morphism with Nagata target `S` and
reduced source `X`. Then the relative normalization morphism `f.fromNormalization` is finite. -/
@[stacks 03GR] #check
  (AlgebraicGeometry.Scheme.Hom.isFinite_fromNormalization_of_nagata_of_finiteType :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [Scheme.Hom.FiniteType f]
      [Scheme.Nagata S] [IsReduced X],
      IsFinite f.fromNormalization)
