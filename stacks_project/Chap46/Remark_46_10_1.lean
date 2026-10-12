/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.DerivedAdeq.Comparison

universe u

/- Remark 46.10.1: for a scheme `S`, the categories `DerivedAdeq S τ` attached to any two
standard topologies are canonically equivalent, via their canonical derived pullbacks to the
common big fppf site. -/
@[stacks 070V] #check (SheafOfModules.DerivedAdeq.toFppf_isEquivalence :
  ∀ (S : AlgebraicGeometry.Scheme.{u}) (τ : AlgebraicGeometry.StandardTopology),
    CategoryTheory.Functor.IsEquivalence (SheafOfModules.DerivedAdeq.toFppf S τ))
