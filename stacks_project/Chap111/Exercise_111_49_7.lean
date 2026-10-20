/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AffineQuadricCone.Cartier

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.AffineQuadricCone
open Scheme

universe u

/- Exercise 111.49.7 (1): the ruling divisor on the affine quadric cone
is not the Weil divisor associated to any Cartier divisor. -/
@[stacks 02FA] #check
  (AlgebraicGeometry.AffineQuadricCone.rulingWeilDivisor_not_ofCartier :
    ∀ (k : Type u) [Field k]
      [HasSheafify (Opens.grothendieckTopology (scheme k).toTopCat) AddCommGrpCat.{u}]
      [(Opens.grothendieckTopology (scheme k).toTopCat).HasSheafCompose
        (forget CommRingCat.{u})]
      (τ : CartierDivisor (scheme k)),
      weilDivisor_ofCartier τ ≠ rulingWeilDivisor k)

/- Exercise 111.49.7 (2): no natural multiple nD with 1 < n is the
Weil divisor associated to a Cartier divisor. -/
@[stacks 02FA] #check
  (AlgebraicGeometry.AffineQuadricCone.nsmul_rulingWeilDivisor_not_ofCartier :
    ∀ (k : Type u) [Field k] {n : ℕ} (hn : 1 < n)
      [HasSheafify (Opens.grothendieckTopology (scheme k).toTopCat) AddCommGrpCat.{u}]
      [(Opens.grothendieckTopology (scheme k).toTopCat).HasSheafCompose
        (forget CommRingCat.{u})]
      (τ : CartierDivisor (scheme k)),
      weilDivisor_ofCartier τ ≠ n • rulingWeilDivisor k)
