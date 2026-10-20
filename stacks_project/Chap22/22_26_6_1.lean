/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.HomComplex.Differential
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CochainComplex.HomComplex

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {F G : CochainComplex C ℤ} {n m : ℤ}
variable (hnm : n + 1 = m) (z : Cochain F G n)
variable (p q : ℤ) (hpq : p + m = q) (q₁ q₂ : ℤ)
variable (hq₁ : q₁ = q - 1) (hq₂ : p + 1 = q₂)
variable (hpq₁ : p + n = q₁) (hq₂q : q₂ + n = q)

-- Canonical owner check: the source-facing content is the homogeneous-component sign formula
-- for the differential in the canonical Hom complex. The core owner is `δ_v`, and the degree-`0`
-- specialization used immediately below is the companion owner `δ_zero_cochain_v`. As in the
-- Chapter 15 analogue, this file checks the owners directly instead of adding a local wrapper.

/- Equation 22.26.6.1 (09LA): for a homogeneous component `f_{p, q}` in the Hom complex, the differential is
`d_B ≫ f_{p, q} - (-1)^(p + q) f_{p, q} ≫ d_A`; in mathlib this is the canonical component formula
`δ_v` for the differential on `CochainComplex.HomComplex`, with
`p + q` interpreted as the total cochain degree of `f_{p, q}`. -/
@[stacks 09LA] #check
  (δ_v n m hnm z p q hpq q₁ q₂ hq₁ hq₂ :
    (δ n m z).v p q hpq =
      z.v p q₁ hpq₁ ≫ G.d q₁ q +
        m.negOnePow • F.d p q₂ ≫ z.v q₂ q hq₂q)

/- Companion specialization: in total degree `0`, the same Hom-complex formula specializes to
the standard Leibniz rule for degree-`0` cochains. -/
#check @δ_zero_cochain_v
