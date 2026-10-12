/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.GroupScheme.Properties

open CategoryTheory AlgebraicGeometry

universe u

/- Definition 39.4.5 (1): A group scheme `G` over `S` is smooth when its structure
morphism `G.X.hom` is smooth. -/
@[stacks 047E] #check (AlgebraicGeometry.GroupScheme.Smooth :
  {S : Scheme.{u}} → Grp (Over S) → Prop)

/- Definition 39.4.5 (2): A group scheme `G` over `S` is flat when its structure
morphism `G.X.hom` is flat. -/
@[stacks 047E] #check (AlgebraicGeometry.GroupScheme.Flat :
  {S : Scheme.{u}} → Grp (Over S) → Prop)

/- Definition 39.4.5 (3): A group scheme `G` over `S` is separated when its structure
morphism `G.X.hom` is separated. -/
@[stacks 047E] #check (AlgebraicGeometry.GroupScheme.IsSeparated :
  {S : Scheme.{u}} → Grp (Over S) → Prop)
