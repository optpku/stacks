/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Integral.Extension
import StacksCheckRecall

/-!
# Extending an integral morphism along a quasi-compact open immersion

An integral morphism of algebraic spaces along a quasi-compact open immersion
extends to an integral morphism of the ambient space, recovering the original
source as the inverse image of that open.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 68.9.1: Let `S` be a scheme. Let `j : V ⟶ Y` be a quasi-compact open
immersion of algebraic spaces over `S`. Let `π : Z ⟶ V` be an integral morphism.
Then there exists an integral morphism `ν : Y' ⟶ Y` such that `Z` is
`V`-isomorphic to the inverse image of `V` in `Y'`. -/
@[stacks 0G2D] #check
  (AlgebraicGeometry.AlgebraicSpace.exists_isIntegralHom_isPullback :
    ∀ {S : Scheme.{u}}
    {V Y Z : AlgebraicSpace S} (j : V ⟶ Y) [IsOpenImmersion j] [QuasiCompact j]
    (π : Z ⟶ V) [IsIntegralHom π],
    ∃ (Y' : AlgebraicSpace S) (ν : Y' ⟶ Y) (hν : IsIntegralHom ν) (μ : Z ⟶ Y'),
      IsPullback μ π ν j)

end AlgebraicGeometry.AlgebraicSpace
