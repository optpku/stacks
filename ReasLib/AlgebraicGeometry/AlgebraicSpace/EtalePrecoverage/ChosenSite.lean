/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChosenSite
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtalePrecoverage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtalePrecoverage.Stability
public import ReasLib.CategoryTheory.Sites.IndexedSite.CardinalRank

/-!
# Chosen big étale sites of algebraic spaces

A chosen big étale site is a cardinal truncation of the étale precoverage
that satisfies the site axioms and represents every étale covering up to
combinatorial equivalence.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- The étale covering class of algebraic spaces over `S` satisfies the site
axioms. -/
instance etalePrecoverage.instIsSite :
    (etalePrecoverage : Precoverage (AlgebraicSpace S)).IsSite :=
  sorry

/-- A big étale site of algebraic spaces over `S` is a chosen big site for the
étale covering class. -/
abbrev ChosenBigEtaleSite (S : Scheme.{u}) :=
  ChosenBigSite (etalePrecoverage : Precoverage (AlgebraicSpace S))

/-- A chosen big étale site of algebraic spaces exists over every scheme. -/
theorem ChosenBigEtaleSite.exists (S : Scheme.{u}) :
    Nonempty (ChosenBigEtaleSite S) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
