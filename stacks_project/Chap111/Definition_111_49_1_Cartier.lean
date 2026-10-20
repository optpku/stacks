/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.Cartier

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Cartier divisors are global sections of the quotient of meromorphic units by regular units. -/
#check (AlgebraicGeometry.Scheme.CartierDivisor :
  (S : Scheme.{u}) →
    [HasSheafify (Opens.grothendieckTopology S.toTopCat) AddCommGrpCat.{u}] →
    [(Opens.grothendieckTopology S.toTopCat).HasSheafCompose
      (CategoryTheory.forget CommRingCat.{u})] → Type u)
