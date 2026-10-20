/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.PolynomialSite

/-!
# Polynomial algebras and the opposite site C_{B/A}

The polynomial over-category and its opposite site are provided by the shared owner.
-/

@[expose] public section

open CategoryTheory

universe u

#check (Algebra.PolynomialOver :
  (A B : Type u) → [CommRing A] → [CommRing B] → [Algebra A B] → Type (u + 1))

#check (Algebra.PolynomialSite :
  (A B : Type u) → [CommRing A] → [CommRing B] → [Algebra A B] → Type (u + 1))
