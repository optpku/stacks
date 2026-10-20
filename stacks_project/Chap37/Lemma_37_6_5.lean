/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FormallyUnramified.Restriction
import StacksCheckRecall

open CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 37.6.5: The restriction of a formally unramified morphism to compatible open
subschemes of its source and target is formally unramified. -/
@[stacks 02HC] #check (@AlgebraicGeometry.FormallyUnramified.resLE :
  ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S) (U : X.Opens) (V : S.Opens)
    (e : U ≤ f ⁻¹ᵁ V) [AlgebraicGeometry.FormallyUnramified f],
      AlgebraicGeometry.FormallyUnramified (f.resLE V U e))
