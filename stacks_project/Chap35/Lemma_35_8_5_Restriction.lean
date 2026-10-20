/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Restriction

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

/- This compatibility bridge re-exports the canonical restriction morphisms
between standard scheme sites from their mathematical owner. -/
#check (AlgebraicGeometry.Scheme.SiteRestriction.bigToZariski :
  ∀ (τ : StandardTopology) (S : Scheme.{u}),
    RingedSite.Hom (StandardTopology.Big.ringedSite τ S)
      (AlgebraicGeometry.Scheme.Zariski.Small.ringedSite S))
