/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Proper
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Definition 87.31.1: a morphism `f : Y ⟶ X` of formal algebraic spaces over a
scheme `S` is proper if it is representable by algebraic spaces and is proper
in the sense of Bootstrap, Definition 80.4.1. -/
@[stacks 0AM6] #check
  (AlgebraicGeometry.FormalAlgebraicSpace.Proper :
    ∀ {S : AlgebraicGeometry.Scheme.{u}}
      {X Y : (CategoryTheory.Over S)ᵒᵖ ⥤ Type u},
      (X ⟶ Y) → Prop)
