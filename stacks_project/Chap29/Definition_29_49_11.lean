/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Birational.Birational
import StacksCheckRecall

@[expose] public section

universe u

variable (X Y : AlgebraicGeometry.Scheme.{u})
variable [IrreducibleSpace X] [IrreducibleSpace Y]

/- Definition 29.49.11 (1): Two irreducible schemes are birational when they are isomorphic
in the category of irreducible schemes and dominant rational maps. -/
@[stacks 0A20] #check (AlgebraicGeometry.Scheme.Birational X Y : Prop)

variable (S : AlgebraicGeometry.Scheme.{u}) (sX : X ⟶ S) (sY : Y ⟶ S)

/- Definition 29.49.11 (2): Two irreducible schemes over `S` are `S`-birational when they
are isomorphic in the category of irreducible schemes over `S` and dominant `S`-rational maps. -/
@[stacks 0A20] #check (AlgebraicGeometry.Scheme.BirationalOver sX sY : Prop)
