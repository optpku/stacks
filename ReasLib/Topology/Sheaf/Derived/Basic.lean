/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Derived
public import ReasLib.Topology.Sheaves.Abelian
public import ReasLib.Topology.Sheaves.Abelian.Sheafification
import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived categories of abelian sheaves

This file reexports the site-level homology and derived-category instances for abelian sheaves and
records their specialization to topological spaces. Downstream derived constructions therefore do
not need local installations of `HasDerivedCategory.standard`.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace TopCat

/-- Abelian-group-valued sheaves on a topological space carry the canonical derived-category
structure coming from the opens-site sheafification. -/
@[stacks 01DP "topological abelian-sheaf derived category"]
noncomputable instance addCommGrpHasDerivedCategory (X : TopCat.{u}) :
    HasDerivedCategory (X.Sheaf AddCommGrpCat.{u}) :=
  CategoryTheory.AbelianSheaf.hasDerivedCategory (Opens.grothendieckTopology X)

end TopCat
