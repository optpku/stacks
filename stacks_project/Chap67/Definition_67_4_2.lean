/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation
public import stacks_project.Chap67.Definition_67_4_2_Separation
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Definition 67.4.2 (1): a morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S` is
separated if the relative diagonal `diagonal f` is a closed immersion. -/
@[stacks 03HL] #check (AlgebraicGeometry.AlgebraicSpace.Separated :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}, (X ⟶ Y) → Prop)

/- Definition 67.4.2 (2): a morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S` is
locally separated if the relative diagonal `diagonal f` is an immersion. This does not include
quasi-separatedness. -/
@[stacks 03HL] #check (AlgebraicGeometry.AlgebraicSpace.LocallySeparated :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}, (X ⟶ Y) → Prop)

/- Definition 67.4.2 (3): a morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S` is
quasi-separated if the relative diagonal `diagonal f` is quasi-compact. -/
@[stacks 03HL] #check (AlgebraicGeometry.AlgebraicSpace.QuasiSeparated :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}, (X ⟶ Y) → Prop)
