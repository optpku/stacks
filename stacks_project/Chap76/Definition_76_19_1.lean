/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FormallySmooth
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Definition 76.19.1: Let `S` be a scheme. A morphism `f : X ⟶ Y` of algebraic
spaces over `S` is said to be formally smooth if it is formally smooth as a
transformation of functors as in Definition 76.13.1. -/
@[stacks 060G]
#check (AlgebraicGeometry.AlgebraicSpace.FormallySmooth :
    {S : Scheme.{u}} → {X Y : AlgebraicSpace S} → (X ⟶ Y) → Prop)
