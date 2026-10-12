/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Sites.Presentation
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.AlgebraicGeometry.Sites.Fpqc

@[expose] public section

universe u v

set_option pp.universes true in
#check @AlgebraicGeometry.ChosenBigSite.IsContainedIn

/- Lemma 34.12.1: Every universe-small family of chosen big Zariski-site
presentations is contained in a common chosen presentation. -/
@[stacks 022J] #check
  (AlgebraicGeometry.ChosenBigSite.exists_common.{u, v}
      AlgebraicGeometry.Scheme.zariskiPrecoverage :
    ∀ {ι : Type u}
      (X : ι → AlgebraicGeometry.ChosenBigZariskiSite.{u, v}),
      ∃ Y : AlgebraicGeometry.ChosenBigZariskiSite.{u, u},
        ∀ i, AlgebraicGeometry.ChosenBigSite.IsContainedIn.{u, v, u} (X i) Y)

#check
  (AlgebraicGeometry.ChosenBigSite.exists_common.{u, v}
      AlgebraicGeometry.Scheme.fppfPrecoverage :
    ∀ {ι : Type u}
      (X : ι → AlgebraicGeometry.ChosenBigSite.{u, v}
        AlgebraicGeometry.Scheme.fppfPrecoverage),
      ∃ Y : AlgebraicGeometry.ChosenBigSite.{u, u}
          AlgebraicGeometry.Scheme.fppfPrecoverage,
        ∀ i, AlgebraicGeometry.ChosenBigSite.IsContainedIn.{u, v, u} (X i) Y)

#check
  (AlgebraicGeometry.ChosenBigSite.exists_common.{u, v}
      AlgebraicGeometry.Scheme.etalePrecoverage :
    ∀ {ι : Type u}
      (X : ι → AlgebraicGeometry.ChosenBigSite.{u, v}
        AlgebraicGeometry.Scheme.etalePrecoverage),
      ∃ Y : AlgebraicGeometry.ChosenBigSite.{u, u}
          AlgebraicGeometry.Scheme.etalePrecoverage,
        ∀ i, AlgebraicGeometry.ChosenBigSite.IsContainedIn.{u, v, u} (X i) Y)
