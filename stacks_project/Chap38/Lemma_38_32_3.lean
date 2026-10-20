/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Compactification.CalculusOfFractions

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Compactification

/- Lemma 38.32.3: for a quasi-compact quasi-separated scheme `S`, compactification morphisms
whose interior component is an isomorphism form a right multiplicative system. -/
@[stacks 0ATV] #check
  (AlgebraicGeometry.Scheme.Compactification.hasRightCalculusOfFractions :
    ∀ (S : Scheme.{u}) [CompactSpace S] [QuasiSeparatedSpace S],
      (interiorIsomorphisms S).HasRightCalculusOfFractions)

end AlgebraicGeometry.Scheme.Compactification
