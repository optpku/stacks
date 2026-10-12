/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Definition 67.20.2: a morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S` is
affine if for every affine scheme `Z` and morphism `Z ⟶ Y`, the fibre product `X ×_Y Z`
is representable by an affine scheme. -/
@[stacks 03WF] #check (AlgebraicGeometry.AlgebraicSpace.Affine :
  ∀ {S : AlgebraicGeometry.Scheme.{u}}
    {X Y : AlgebraicGeometry.AlgebraicSpace S},
    (X ⟶ Y) → Prop)
