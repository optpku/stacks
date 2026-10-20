/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.UniversallyCatenary.Stalk
import StacksCheckRecall

universe u

/- Lemma 29.17.3: For a locally Noetherian scheme, universal catenarity is equivalent to
universal catenarity of every stalk ring. -/
@[stacks 02JA] #check
  (AlgebraicGeometry.UniversallyCatenary.iff_forall_stalk :
    ∀ (S : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsLocallyNoetherian S],
      AlgebraicGeometry.UniversallyCatenary S ↔
        ∀ s : S, UniversallyCatenaryRing.{u, u} (S.presheaf.stalk s))
