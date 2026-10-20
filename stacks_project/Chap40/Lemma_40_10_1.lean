/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.GroupoidScheme.Topology

@[expose] public section

open AlgebraicGeometry

universe u

/- Lemma 40.10.1: if the object scheme of a groupoid scheme is the spectrum of a field,
then its composition morphism is open. -/
@[stacks 04LM] #check
  (AlgebraicGeometry.GroupoidScheme.isOpenMap_c :
    ∀ {S : Scheme.{u}} (G : AlgebraicGeometry.GroupoidScheme S) {k : Type u} [Field k],
      (Spec (CommRingCat.of k) ≅ G.U.left) → IsOpenMap G.c.left)
