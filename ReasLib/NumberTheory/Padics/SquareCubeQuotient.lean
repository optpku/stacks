/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.LinearAlgebra.Prod
public import Mathlib.NumberTheory.Padics.RingHoms
public import ReasLib.Algebra.Module.End.FiniteLength

@[expose] public section

noncomputable section

namespace PadicInt

open IsLocalRing

variable (p : ℕ) [Fact p.Prime]

/-- The product of the quotients of the `p`-adic integers by the square and cube of
its maximal ideal. -/
abbrev SquareCubeQuotient :=
  (ℤ_[p] ⧸ maximalIdeal ℤ_[p] ^ 2) × (ℤ_[p] ⧸ maximalIdeal ℤ_[p] ^ 3)

/-- The endomorphism of the square-cube quotient product represented by the block matrix
`((a, b), (p * c, d))`. -/
def squareCubeBlockEnd (a : ℤ_[p]ˣ) (b c : ℤ_[p]) (d : ℤ_[p]ˣ) :
    Module.End ℤ_[p] (SquareCubeQuotient p) :=
  let diagonalA :=
    LinearMap.lsmul ℤ_[p] (ℤ_[p] ⧸ maximalIdeal ℤ_[p] ^ 2) (a : ℤ_[p])
  let upperRight := Submodule.mapQ (maximalIdeal ℤ_[p] ^ 3)
    (maximalIdeal ℤ_[p] ^ 2) (LinearMap.lsmul ℤ_[p] ℤ_[p] b) (by
      rw [maximalIdeal_eq_span_p]
      intro x hx
      change b * x ∈ Ideal.span {(p : ℤ_[p])} ^ 2
      rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hx ⊢
      obtain ⟨y, rfl⟩ := hx
      refine ⟨(p : ℤ_[p]) * b * y, ?_⟩
      ring)
  let lowerLeft := Submodule.mapQ (maximalIdeal ℤ_[p] ^ 2)
    (maximalIdeal ℤ_[p] ^ 3) (LinearMap.lsmul ℤ_[p] ℤ_[p] ((p : ℤ_[p]) * c)) (by
      rw [maximalIdeal_eq_span_p]
      intro x hx
      change ((p : ℤ_[p]) * c) * x ∈ Ideal.span {(p : ℤ_[p])} ^ 3
      rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hx ⊢
      obtain ⟨y, rfl⟩ := hx
      refine ⟨c * y, ?_⟩
      ring)
  let diagonalD :=
    LinearMap.lsmul ℤ_[p] (ℤ_[p] ⧸ maximalIdeal ℤ_[p] ^ 3) (d : ℤ_[p])
  (diagonalA.coprod upperRight).prod (lowerLeft.coprod diagonalD)

/-- On quotient representatives, `squareCubeBlockEnd` acts by
`(x, y) ↦ (a * x + b * y, p * c * x + d * y)`. -/
theorem squareCubeBlockEnd_mk (a : ℤ_[p]ˣ) (b c : ℤ_[p]) (d : ℤ_[p]ˣ)
    (x y : ℤ_[p]) :
    squareCubeBlockEnd p a b c d
        ((maximalIdeal ℤ_[p] ^ 2).mkQ x, (maximalIdeal ℤ_[p] ^ 3).mkQ y) =
      ((maximalIdeal ℤ_[p] ^ 2).mkQ ((a : ℤ_[p]) * x + b * y),
        (maximalIdeal ℤ_[p] ^ 3).mkQ
          ((p : ℤ_[p]) * c * x + (d : ℤ_[p]) * y)) := sorry

/-- The product of the square and cube quotients of the `p`-adic integers has finite length. -/
theorem squareCubeQuotient_isFiniteLength :
    IsFiniteLength ℤ_[p] (SquareCubeQuotient p) := sorry

/-- After identifying the residue field of the `p`-adic integers with `ZMod p`, the
finite-length determinant of `squareCubeBlockEnd p a b c d` is the reduction of
`a ^ 2 * d ^ 3`. -/
theorem finiteLengthDeterminant_squareCubeBlockEnd
    (a : ℤ_[p]ˣ) (b c : ℤ_[p]) (d : ℤ_[p]ˣ) :
    residueField
        ((squareCubeBlockEnd p a b c d).finiteLengthDeterminant
          (squareCubeQuotient_isFiniteLength p)) =
      (Units.map toZMod.toMonoidHom (a ^ 2 * d ^ 3)).val := sorry

end PadicInt
