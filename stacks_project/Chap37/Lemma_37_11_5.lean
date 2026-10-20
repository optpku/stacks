/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FormallySmooth.Restriction
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 37.11.5: The restriction of a formally smooth morphism to open subschemes
of its source and target is formally smooth. -/
@[stacks 02H3] #check (@AlgebraicGeometry.FormallySmooth.resLE :
  ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S) (U : X.Opens) (V : S.Opens)
    (e : U ≤ f ⁻¹ᵁ V) [AlgebraicGeometry.FormallySmooth f],
      AlgebraicGeometry.FormallySmooth (f.resLE V U e))
