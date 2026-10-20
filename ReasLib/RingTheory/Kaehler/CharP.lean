/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.RingTheory.Kaehler.Polynomial
public import ReasLib.Algebra.CharP.RingHom
public import ReasLib.RingTheory.Polynomial.CharP
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Prime-field Kähler base change in characteristic `p`

This leaf owns the canonical Kähler base-change map for the prime-field tower
associated to a characteristic-`p` field extension.

@stack 031X
@stack 00TY
-/

@[expose] public section

open scoped TensorProduct

universe u v

namespace KaehlerDifferential.CharP

/-- In characteristic `p`, the universal Kähler differential of `X^p` over
`R` vanishes in the polynomial algebra `R[X]`. -/
@[simp]
theorem D_X_pow_eq_zero {R : Type u} [CommRing R] {p : ℕ} [CharP R p] :
    KaehlerDifferential.D R (Polynomial R) (Polynomial.X ^ p) = 0 := by
  rw [KaehlerDifferential.polynomial_D_apply, Polynomial.derivative_X_pow_eq_zero]
  exact zero_smul _ _

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Nontrivial S] [Algebra R S]
variable {p : ℕ} [Fact p.Prime] [CharP R p]

/-- Tag `031X`: the Kähler base-change map along the canonical prime-field
tower `ZMod p → R → S`. The `ZMod` algebra structures are canonical under the
given characteristic hypothesis but deliberately remain internal to this data
owner, since they are not globally registered instances. -/
@[stacks 031X "prime-field Kähler base-change map"]
noncomputable def primeFieldMapBaseChange :
    letI : Algebra (ZMod p) R := ZMod.algebra R p
    letI : CharP S p := CharP.of_ringHom_of_prime (algebraMap R S) p Fact.out
    letI : Algebra (ZMod p) S := ZMod.algebra S p
    letI : IsScalarTower (ZMod p) R S := inferInstance
    S ⊗[R] Ω[R⁄ZMod p] →ₗ[S] Ω[S⁄ZMod p] :=
  letI : Algebra (ZMod p) R := ZMod.algebra R p
  letI : CharP S p := CharP.of_ringHom_of_prime (algebraMap R S) p Fact.out
  letI : Algebra (ZMod p) S := ZMod.algebra S p
  letI : IsScalarTower (ZMod p) R S := inferInstance
  KaehlerDifferential.mapBaseChange (ZMod p) R S

end KaehlerDifferential.CharP
