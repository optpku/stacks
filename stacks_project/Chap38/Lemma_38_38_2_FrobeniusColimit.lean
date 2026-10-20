/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.H.FrobeniusColimit

@[expose] public section

open CategoryTheory

universe u

/- Compatibility check for the canonical Frobenius-colimit h-sheaf construction. -/
#check
  (AlgebraicGeometry.ChosenBigHSite.FrobeniusColimit.sheaf :
    ∀ (p : ℕ) [Fact p.Prime]
      (Schh : AlgebraicGeometry.ChosenBigHSite.{u, u}) (S : Schh.carrier)
      [AlgebraicGeometry.Scheme.IsCharP (Schh.toScheme.obj S) p],
      Sheaf (AlgebraicGeometry.ChosenBigHSite.bigTopology Schh S) RingCat.{u})
