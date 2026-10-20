/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PhPrecoverage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChosenSite

/-!
# Chosen big ph sites of algebraic spaces

A chosen big ph site is a cardinal truncation of the ph precoverage that is a
site and represents every ph covering up to combinatorial equivalence.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A big ph site of algebraic spaces over `S` is a chosen big site for the ph
covering class. -/
abbrev ChosenBigPhSite (S : Scheme.{u}) :=
  ChosenBigSite (phPrecoverage : Precoverage (AlgebraicSpace S))

/-- A chosen big ph site of algebraic spaces exists over every scheme. -/
theorem ChosenBigPhSite.exists (S : Scheme.{u}) :
    Nonempty (ChosenBigPhSite S) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
