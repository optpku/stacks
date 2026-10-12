/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic.UniversallyOpen
import StacksCheckRecall

open AlgebraicGeometry

universe u

/-
Lemma 29.30.8: A syntomic morphism is universally open.
-/
@[stacks 056F] #check (AlgebraicGeometry.Syntomic.universallyOpen :
  ∀ {X S : Scheme.{u}} {f : X ⟶ S},
    AlgebraicGeometry.Syntomic f → AlgebraicGeometry.UniversallyOpen f)
