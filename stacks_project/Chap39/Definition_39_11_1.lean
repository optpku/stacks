/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import Mathlib.AlgebraicGeometry.Pullbacks
import ReasLib.CategoryTheory.Monoidal.Cartesian.PseudoTorsor
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory

universe u

variable (S : Scheme.{u}) (G : Grp (Over S))

/- Definition 39.11.1 (1): The `G`-action on `X` is a pseudo `G`-torsor, or formally
principally homogeneous, when `(g, x) ↦ (g • x, x)` is an isomorphism over `S`. -/
@[stacks 0498] #check
  (CategoryTheory.Mod.IsPseudoTorsor : Mod (Over S) G.X → Prop)

/- Definition 39.11.1 (2): A pseudo `G`-torsor is trivial when it is equivariantly
isomorphic over `S` to `G` with its regular left action. -/
@[stacks 0498] #check
  (CategoryTheory.Mod.IsTrivial : Mod (Over S) G.X → Prop)
