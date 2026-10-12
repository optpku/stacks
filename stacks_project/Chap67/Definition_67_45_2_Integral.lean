/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Finite
public import stacks_project.Chap65.Definition_65_6_3_Hom
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Definition 67.45.2 (1): a morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S`
is integral if for every affine scheme `Z` and morphism `Z ⟶ Y` the algebraic space
`X ×_Y Z` is representable by an affine scheme integral over `Z`. -/
@[stacks 03ZP] #check (AlgebraicGeometry.AlgebraicSpace.IsIntegralHom :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicGeometry.AlgebraicSpace S},
    (X ⟶ Y) → Prop)

/- Definition 67.45.2 (2): a morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S`
is finite if for every affine scheme `Z` and morphism `Z ⟶ Y` the algebraic space
`X ×_Y Z` is representable by an affine scheme finite over `Z`. -/
@[stacks 03ZP] #check (AlgebraicGeometry.AlgebraicSpace.IsFinite :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicGeometry.AlgebraicSpace S},
    (X ⟶ Y) → Prop)
