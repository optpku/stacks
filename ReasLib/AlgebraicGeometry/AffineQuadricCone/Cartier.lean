/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AffineQuadricCone.Ruling
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.Cartier.Weil
import Mathlib.Tactic.CrossRefAttribute

/-!
# A Weil divisor on the affine quadric cone that is not Q-Cartier

The ruling Weil divisor `[x = 0, z = 0]` on the affine quadric cone
`x * y - z * w = 0` in affine 4-space is not associated to any Cartier
divisor, nor is any positive multiple `n • D` with `1 < n`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.AffineQuadricCone
open Scheme

universe u

namespace AlgebraicGeometry.AffineQuadricCone

/-- The ruling Weil divisor `D = [x = 0, z = 0]` on the
affine quadric cone variety `X : x * y - z * w = 0` in `AffineSpaceOverField k 4`
is not the Weil divisor associated to any Cartier divisor. -/
@[stacks 02FA]
theorem rulingWeilDivisor_not_ofCartier (k : Type u) [Field k]
    [HasSheafify (Opens.grothendieckTopology (scheme k).toTopCat) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology (scheme k).toTopCat).HasSheafCompose
      (forget CommRingCat.{u})]
    (τ : CartierDivisor (scheme k)) :
    weilDivisor_ofCartier τ ≠ rulingWeilDivisor k := sorry

/-- For every natural number `n` with `1 < n`, the multiple
`n • D` of the ruling Weil divisor on the affine quadric cone variety is not the
Weil divisor associated to any Cartier divisor. -/
@[stacks 02FA]
theorem nsmul_rulingWeilDivisor_not_ofCartier (k : Type u) [Field k] {n : ℕ}
    (hn : 1 < n)
    [HasSheafify (Opens.grothendieckTopology (scheme k).toTopCat) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology (scheme k).toTopCat).HasSheafCompose
      (forget CommRingCat.{u})]
    (τ : CartierDivisor (scheme k)) :
    weilDivisor_ofCartier τ ≠ n • rulingWeilDivisor k := sorry

end AlgebraicGeometry.AffineQuadricCone
