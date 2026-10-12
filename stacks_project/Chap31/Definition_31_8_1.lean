/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.WeaklyAssociatedPoints.Relative

@[expose] public section

universe u

/- Definition 31.8.1: the relative weak assassin is the union, over all points of the base, of
the images of the weak assassins of the module restrictions to the scheme-theoretic fibers. -/
@[stacks 05AV] #check (AlgebraicGeometry.Scheme.Modules.relativeWeakAss :
  ∀ {X S : AlgebraicGeometry.Scheme.{u}}, (X ⟶ S) → X.Modules → Set X)
