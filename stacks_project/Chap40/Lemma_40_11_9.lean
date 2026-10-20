/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.GroupoidScheme.RelationImage

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.GroupoidScheme

/-
Lemma 40.11.9: if the object scheme of a groupoid scheme is the spectrum of a field
and its arrow scheme is quasi-compact, the scheme-theoretic image of `(t, s)` admits
composition, identity, and inverse maps satisfying the groupoid laws with the canonical
restricted projections to `G.U`.
-/
@[stacks 04QD] #check
  (AlgebraicGeometry.GroupoidScheme.relationImage :
    ∀ {S : Scheme.{u}} {k : Type u} [Field k] (G : GroupoidScheme S),
      (Spec (CommRingCat.of k) ≅ G.U.left) → [CompactSpace G.R.left] →
        ∃ c e i, Hom.IsImageGroupoid (toPair G) c e i)

end AlgebraicGeometry.GroupoidScheme
