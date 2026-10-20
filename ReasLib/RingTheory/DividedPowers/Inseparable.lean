/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Polynomial.Basic
public import ReasLib.RingTheory.DividedPowers.Polynomial

@[expose] public section

universe u

namespace DividedPowers.Inseparable

/-- The divided-power polynomial presentation `D[z]⟨ξ⟩ / (ξ - (z^p - lam))` before
`p`-adic completion. -/
noncomputable abbrev adjoin {D : Type u} [CommRing D] (p : ℕ) (lam : D) : Type u :=
  DPPolynomial (Polynomial D) PUnit.{u + 1} ⧸
    Ideal.span
      {DPPolynomial.X (Polynomial D) PUnit.unit -
        algebraMap (Polynomial D) (DPPolynomial (Polynomial D) PUnit.{u + 1})
          (Polynomial.X ^ p - Polynomial.C lam)}

/-- The structure map `D → D[z]⟨ξ⟩ / (ξ - (z^p - lam))`. -/
noncomputable def toAdjoin {D : Type u} [CommRing D] (p : ℕ) (lam : D) :
    D →+* adjoin p lam :=
  (Ideal.Quotient.mk
      (Ideal.span
        {DPPolynomial.X (Polynomial D) PUnit.unit -
          algebraMap (Polynomial D) (DPPolynomial (Polynomial D) PUnit.{u + 1})
            (Polynomial.X ^ p - Polynomial.C lam)})).comp
    ((algebraMap (Polynomial D) (DPPolynomial (Polynomial D) PUnit.{u + 1})).comp
      (algebraMap D (Polynomial D)))

/-- Evaluation of the structure map on a coefficient of `D`. -/
theorem toAdjoin_apply {D : Type u} [CommRing D] (p : ℕ) (lam : D)
    (x : D) :
    toAdjoin p lam x =
      Ideal.Quotient.mk _
        (algebraMap (Polynomial D) (DPPolynomial (Polynomial D) PUnit.{u + 1})
          (algebraMap D (Polynomial D) x)) :=
  rfl

/-- The `p`-adic completion of the divided-power quotient `adjoin p lam`. -/
noncomputable abbrev completion {D : Type u} [CommRing D] (p : ℕ) (lam : D) :
    Type u :=
  AdicCompletion (Ideal.span {(p : adjoin p lam)}) (adjoin p lam)

/-- The structure map `D → D'` through `p`-adic completion. -/
noncomputable def toCompletion
    {D : Type u} [CommRing D] (p : ℕ) (lam : D) :
    D →+* completion p lam :=
  (algebraMap (adjoin p lam) (completion p lam)).comp
    (toAdjoin p lam)

/-- Evaluation of the completed structure map. -/
theorem toCompletion_apply
    {D : Type u} [CommRing D] (p : ℕ) (lam : D) (x : D) :
    toCompletion p lam x =
      algebraMap (adjoin p lam) (completion p lam)
        (toAdjoin p lam x) :=
  rfl


/-- The image of `Polynomial.X` in `D'`. -/
noncomputable def z {D : Type u} [CommRing D] (p : ℕ) (lam : D) :
    completion p lam :=
  algebraMap (adjoin p lam) (completion p lam)
    (Ideal.Quotient.mk _
      (algebraMap (Polynomial D) (DPPolynomial (Polynomial D) PUnit.{u + 1}) Polynomial.X))

/-- `D`-algebra structure on the completed inseparable adjoin. -/
noncomputable instance algebra
    {D : Type u} [CommRing D] {p : ℕ} {lam : D} :
    Algebra D (completion p lam) :=
  inferInstanceAs (Algebra D
    (AdicCompletion (Ideal.span {(p : adjoin p lam)}) (adjoin p lam)))

/-- `A`-algebra structure on `D'` via `A → D → D'`. -/
noncomputable instance algebraOver
    {A D : Type u} [CommRing A] [CommRing D] [Algebra A D] {p : ℕ} {lam : D} :
    Algebra A (completion p lam) :=
  inferInstanceAs (Algebra A
    (AdicCompletion (Ideal.span {(p : adjoin p lam)}) (adjoin p lam)))

/-- Scalar tower `A → D → D'`. -/
instance scalarTower
    {A D : Type u} [CommRing A] [CommRing D] [Algebra A D] {p : ℕ} {lam : D} :
    IsScalarTower A D (completion p lam) :=
  ⟨fun a d x ↦ by
    ext n
    exact smul_assoc a d (x.val n)⟩

/-- The image of the formal divided power of the adjoined divided-power coordinate. -/
noncomputable def xiPow {D : Type u} [CommRing D] (p : ℕ) (lam : D) (n : ℕ) :
    completion p lam :=
  algebraMap (adjoin p lam) (completion p lam)
    (Ideal.Quotient.mk _ (DPPolynomial.dp (Polynomial D) n PUnit.unit))

/-- The polynomial coordinate satisfies the defining inseparable divided-power relation. -/
theorem z_pow_sub_eq_xi {D : Type u} [CommRing D] (p : ℕ) (lam : D) :
    z p lam ^ p - toCompletion p lam lam = xiPow p lam 1 := sorry

end DividedPowers.Inseparable
