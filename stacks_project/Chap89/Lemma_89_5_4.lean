/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Blowup.NormalizedDomination
import StacksCheckRecall

/-!
# Domination of proper birational morphisms by normalized blowups

A proper birational morphism into a 2-dimensional Noetherian Nagata algebraic
space is dominated by a finite sequence of normalized closed-point blowups
starting from the canonical normalization of the target.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 89.5.4: Let `S` be a scheme. Let `X` be a Noetherian Nagata algebraic
space over `S` with `dimension X = 2`. Let `f : Y ⟶ X` be a proper birational
morphism. Then there exist an algebraic space `Z` over `S`, a finite sequence
`s : NormalizedBlowupSequence X.normalization Z` of normalized blowups at
closed points, and a morphism `g : Z ⟶ Y` such that
`g ≫ f = s.toSource ≫ X.normalizationTo`. In the source diagram,
`X_0 = X.normalization`, the morphism `X_0 ⟶ X` is `X.normalizationTo`,
each `X_{i+1} ⟶ X_i` is a normalized blowup at a closed point, and
`X_n ⟶ Y` is `g`. -/
@[stacks 0BHM]
#check
  (AlgebraicGeometry.AlgebraicSpace.existsNormalizedBlowupSequence_lift :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S},
      [IsNoetherian X] → [IsNagata X] → [IsDecent Y] →
      [HasFiniteIrreducibleComponents X] → [HasFiniteIrreducibleComponents Y] →
      ∀ (f : Y ⟶ X), [Proper f] → [IsBirational f] → dimension X = 2 →
        ∃ (Z : AlgebraicSpace S) (s : NormalizedBlowupSequence X.normalization Z)
          (g : Z ⟶ Y), g ≫ f = s.toSource ≫ X.normalizationTo)

end AlgebraicGeometry.AlgebraicSpace
