/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.GroupoidScheme.SourceLocus

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Groupoid

export AlgebraicGeometry.GroupoidScheme (exists_open_preimage_eq_sourceLocus)

end AlgebraicGeometry.Scheme.Groupoid

/- Lemma 40.6.1: the `P`-source locus of the source map from the pullback of a
scheme groupoid descends to an open of the base-changed object scheme. -/
@[stacks 04LH] #check
  (AlgebraicGeometry.GroupoidScheme.exists_open_preimage_eq_sourceLocus :
    ∀ {S U' : Scheme.{u}} (G : AlgebraicGeometry.GroupoidScheme S)
      (g : U' ⟶ G.U.left) (P Q R : MorphismProperty Scheme.{u}) (hRQ : R ≤ Q)
      [Q.IsStableUnderBaseChange] [Q.IsStableUnderComposition],
      (∀ {X Y : Scheme.{u}} (f : X ⟶ Y), Q f →
        IsGreatest {W : X.Opens | P (W.ι ≫ f)} (P.sourceLocus f)) →
      (∀ {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {b : Y' ⟶ Y}
        {p : X' ⟶ X} {f' : X' ⟶ Y'}, Q f → R b → IsPullback p f' f b →
        p ⁻¹ᵁ P.sourceLocus f = P.sourceLocus f') →
      R G.s.left → R G.t.left → Q g →
      ∃ W : U'.Opens,
        pullback.fst g G.t.left ⁻¹ᵁ W =
          P.sourceLocus (pullback.snd g G.t.left ≫ G.s.left))
