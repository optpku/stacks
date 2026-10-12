/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.«66_26_0_1_Pushforward»
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

/- 66.26.0.1 (1): a morphism `f : X ⟶ Y` of algebraic spaces induces the pullback functor
`f^* : Mod(𝒪_Y) ⟶ Mod(𝒪_X)` of sheaves of modules on the associated small étale ringed topoi. -/
@[stacks 03LU] #check
  (Modules.pullback :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}, (X ⟶ Y) → Y.Modules ⥤ X.Modules)

/- 66.26.0.1 (2): a morphism `f : X ⟶ Y` of algebraic spaces induces the pushforward functor
`f_* : Mod(𝒪_X) ⟶ Mod(𝒪_Y)` of sheaves of modules on the associated small étale ringed topoi. -/
@[stacks 03LU] #check
  (Modules.pushforward :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}, (X ⟶ Y) → X.Modules ⥤ Y.Modules)
