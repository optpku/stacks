/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap111.Definition_111_49_1_Weil
public import stacks_project.Chap111.Exercise_111_49_7_AffineQuadricCone
public import stacks_project.Chap111.Exercise_111_49_7_Ruling
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

/-- Exercise 111.49.7 (1): the ruling Weil divisor `D = [x = 0, z = 0]` on the
affine quadric cone variety `X : x * y - z * w = 0` in `AffineSpaceOverField k 4`
is not the Weil divisor associated to any Cartier divisor. -/
@[stacks 02FA]
theorem rulingWeilDivisor_not_ofCartier (k : Type u) [Field k]
    [HasSheafify (Opens.grothendieckTopology (scheme k).toTopCat) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology (scheme k).toTopCat).HasSheafCompose
      (forget CommRingCat.{u})]
    (τ : CartierDivisor (scheme k)) :
    weilDivisor_ofCartier τ ≠ rulingWeilDivisor k := sorry

/-- Exercise 111.49.7 (2): for every natural number `n` with `1 < n`, the multiple
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
