/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Sheaf.Cohomology.Cech.Connecting

@[expose] public section

open CategoryTheory Opposite

universe u

/- The coverwise class construction for a chosen lifting cover. -/
#check (@TopCat.Sheaf.Cohomology.Cech.coverwiseClass :
  ∀ {X : TopCat.{u}} {S : ShortComplex (X.Sheaf AddCommGrpCat.{u})}
    {τ : S.X₃.presheaf.obj (op ⊤)} (L : TopCat.Sheaf.Cohomology.Cech.Lift τ),
    (TopCat.Presheaf.cechComplex L.cover.obj S.X₁.presheaf).homology 1)
