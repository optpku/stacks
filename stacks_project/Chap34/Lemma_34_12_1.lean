/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Sites.Presentation

@[expose] public section

universe u v

set_option pp.universes true in
#check @AlgebraicGeometry.ChosenBigSite.IsContainedIn

/- Lemma 34.12.1: Every set of big Zariski sites constructed as in 000J
is contained, on all objects and coverings, in a common big Zariski site.
The same statement holds for fppf and étale sites. -/
@[stacks 022J] #check
  (AlgebraicGeometry.SchAlphaBigSite.exists_common.{u, v}
      AlgebraicGeometry.Scheme.zariskiPrecoverage (Or.inl rfl) :
    ∀ {ι : Type u}
      (X : ι → AlgebraicGeometry.SchAlphaBigSite.{u, v}
        AlgebraicGeometry.Scheme.zariskiPrecoverage),
      ∃ Y : AlgebraicGeometry.SchAlphaBigSite.{u, max (u + 1) v}
          AlgebraicGeometry.Scheme.zariskiPrecoverage,
        ∀ i, AlgebraicGeometry.ChosenBigSite.IsContainedIn (X i).toChosenBigSite
          Y.toChosenBigSite)

#check
  (AlgebraicGeometry.SchAlphaBigSite.exists_common.{u, v}
      AlgebraicGeometry.Scheme.fppfPrecoverage (Or.inr (Or.inl rfl)) :
    ∀ {ι : Type u}
      (X : ι → AlgebraicGeometry.SchAlphaBigSite.{u, v}
        AlgebraicGeometry.Scheme.fppfPrecoverage),
      ∃ Y : AlgebraicGeometry.SchAlphaBigSite.{u, max (u + 1) v}
          AlgebraicGeometry.Scheme.fppfPrecoverage,
        ∀ i, AlgebraicGeometry.ChosenBigSite.IsContainedIn (X i).toChosenBigSite
          Y.toChosenBigSite)

#check
  (AlgebraicGeometry.SchAlphaBigSite.exists_common.{u, v}
      AlgebraicGeometry.Scheme.etalePrecoverage (Or.inr (Or.inr rfl)) :
    ∀ {ι : Type u}
      (X : ι → AlgebraicGeometry.SchAlphaBigSite.{u, v}
        AlgebraicGeometry.Scheme.etalePrecoverage),
      ∃ Y : AlgebraicGeometry.SchAlphaBigSite.{u, max (u + 1) v}
          AlgebraicGeometry.Scheme.etalePrecoverage,
        ∀ i, AlgebraicGeometry.ChosenBigSite.IsContainedIn (X i).toChosenBigSite
          Y.toChosenBigSite)
