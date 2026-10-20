/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Sites.H.FrobeniusColimit
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.ChosenBigHSite.FrobeniusColimit

/-
Lemma 38.38.3: for a prime `p` and a represented characteristic-`p` base `S`,
the sequential colimit of global sections under Frobenius is a sheaf for the chosen
big h topology on schemes over `S`.
-/
@[stacks 0EVL] #check
  (AlgebraicGeometry.ChosenBigHSite.FrobeniusColimit.rawPresheaf_isSheaf :
    ∀ (p : ℕ) [Fact p.Prime] (Schh : ChosenBigHSite.{u, u})
      (S : Schh.carrier) [Scheme.IsCharP (Schh.toScheme.obj S) p],
      Presheaf.IsSheaf (bigTopology Schh S) (rawPresheaf p Schh S))

end AlgebraicGeometry.ChosenBigHSite.FrobeniusColimit
