/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.IntegralClosure.Algebra.Ideal
public import Mathlib.RingTheory.ReesAlgebra
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Integrality over an ideal

This file owns the coefficientwise notion that an element is integral over an
ideal.  Its Rees-algebra characterization is stated through an explicit ring
homomorphism, so consumers do not need to install a polynomial algebra or a
scalar-tower instance locally.
-/

@[expose] public section

universe u v

open Polynomial

namespace ReesAlgebra

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- The coefficient map from the Rees algebra of `I` to `S[X]` induced by a
ring homomorphism `φ : R →+* S`. -/
@[stacks 00H3 "Rees algebra coefficient map"]
noncomputable def polynomialMap (I : Ideal R) (φ : R →+* S) : reesAlgebra I →+* S[X] :=
  (Polynomial.mapRingHom φ).comp (reesAlgebra I).toSubring.subtype

/-- The Rees algebra coefficient map applies `φ` coefficientwise. -/
@[simp, stacks 00H3 "Rees algebra coefficient map evaluation"]
theorem polynomialMap_apply (I : Ideal R) (φ : R →+* S) (p : reesAlgebra I) :
    polynomialMap I φ p = Polynomial.map φ p.1 := sorry
/- Proof strategy: unfold `polynomialMap` and use `Polynomial.coe_mapRingHom`. -/

end ReesAlgebra

namespace RingHom

section Definition

variable {R : Type u} {S : Type v} [CommRing R] [Ring S]

/-- Definition 10.38.1 (Tag 00H2): `g` is integral over `I` along `φ` if it
satisfies a monic equation whose degree-`j` coefficient lies in
`I ^ (P.natDegree - j)`. -/
@[stacks 00H2 "integrality over an ideal"]
def IsIntegralOverIdeal (φ : R →+* S) (I : Ideal R) (g : S) : Prop :=
  ∃ P : R[X], P.Monic ∧ P.eval₂ φ g = 0 ∧
    ∀ j : ℕ, P.coeff j ∈ I ^ (P.natDegree - j)

/-- Integrality over an ideal is monotone in the ideal. -/
@[stacks 00H2 "monotonicity of integrality over an ideal"]
theorem IsIntegralOverIdeal.mono {φ : R →+* S} {I J : Ideal R} {g : S}
    (hg : φ.IsIntegralOverIdeal I g) (hIJ : I ≤ J) :
    φ.IsIntegralOverIdeal J g := sorry
/- Proof strategy: keep the same monic equation and apply `Ideal.pow_right_mono`
to every coefficient condition. -/

/-- Integrality over the unit ideal is ordinary integrality. -/
@[stacks 00H2 "integrality over the unit ideal"]
theorem isIntegralOverIdeal_top_iff (φ : R →+* S) (g : S) :
    φ.IsIntegralOverIdeal ⊤ g ↔ φ.IsIntegralElem g := sorry
/- Proof strategy: the coefficient conditions for powers of `⊤` are vacuous. -/

/-- Integrality over the zero ideal is nilpotence. -/
@[stacks 00H2 "integrality over the zero ideal"]
theorem isIntegralOverIdeal_bot_iff (φ : R →+* S) (g : S) :
    φ.IsIntegralOverIdeal ⊥ g ↔ IsNilpotent g := sorry
/- Proof strategy: a monic polynomial satisfying the zero-ideal coefficient
conditions is a pure power of `X`, including the subsingleton edge case. -/

end Definition

section Rees

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- Lemma 10.38.2 (Tag 00H3): ideal-relative integrality is ordinary
integrality of `C g * X` along the explicit Rees algebra coefficient map. -/
@[stacks 00H3 "integrality over an ideal via the Rees algebra"]
theorem isIntegralOverIdeal_iff_rees (φ : R →+* S) (I : Ideal R) (g : S) :
    φ.IsIntegralOverIdeal I g ↔
      (ReesAlgebra.polynomialMap I φ).IsIntegralElem (C g * X) := sorry
/- Proof strategy: homogenize a coefficientwise monic equation for the forward
direction; for the reverse direction use
`Polynomial.exists_monic_aeval_eq_zero_forall_mem_pow_of_isIntegral`. -/

end Rees

section Operations

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- Zero is integral over every ideal. -/
@[stacks 00H4 "zero is integral over an ideal"]
theorem isIntegralOverIdeal_zero (φ : R →+* S) (I : Ideal R) :
    φ.IsIntegralOverIdeal I 0 := sorry
/- Proof strategy: use `X` as the monic annihilating polynomial. -/

/-- Elements integral over the same ideal are closed under addition. -/
@[stacks 00H4 "addition of elements integral over an ideal"]
theorem IsIntegralOverIdeal.add {φ : R →+* S} {I : Ideal R} {x y : S}
    (hx : φ.IsIntegralOverIdeal I x) (hy : φ.IsIntegralOverIdeal I y) :
    φ.IsIntegralOverIdeal I (x + y) := sorry
/- Proof strategy: use `isIntegralOverIdeal_iff_rees` and closure of integral
elements under addition in `S[X]`. -/

/-- Elements integral over an ideal are closed under negation. -/
@[stacks 00H4 "negation of an element integral over an ideal"]
theorem IsIntegralOverIdeal.neg {φ : R →+* S} {I : Ideal R} {x : S}
    (hx : φ.IsIntegralOverIdeal I x) : φ.IsIntegralOverIdeal I (-x) := sorry
/- Proof strategy: transport the defining monic equation along `X ↦ -X`, or
use the Rees characterization and closure of integral elements under negation. -/

/-- Elements integral over an ideal are closed under subtraction. -/
@[stacks 00H4 "subtraction of elements integral over an ideal"]
theorem IsIntegralOverIdeal.sub {φ : R →+* S} {I : Ideal R} {x y : S}
    (hx : φ.IsIntegralOverIdeal I x) (hy : φ.IsIntegralOverIdeal I y) :
    φ.IsIntegralOverIdeal I (x - y) := sorry
/- Proof strategy: combine `hx.add` with `hy.neg`. -/

/-- Multiplying by an element integral along the same ring homomorphism
preserves integrality over an ideal. -/
@[stacks 00H4 "multiplication by an integral element"]
theorem IsIntegralElem.mul_isIntegralOverIdeal {φ : R →+* S} {I : Ideal R} {x y : S}
    (hx : φ.IsIntegralElem x) (hy : φ.IsIntegralOverIdeal I y) :
    φ.IsIntegralOverIdeal I (x * y) := sorry
/- Proof strategy: map the ordinary integral equation for `x` into `S[X]`,
then multiply integral elements over the Rees algebra. -/

end Operations

section Algebra

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- Base scalar multiplication preserves integrality over an ideal. -/
@[stacks 00H4 "scalar multiplication of an element integral over an ideal"]
theorem IsIntegralOverIdeal.smul {I : Ideal R} {r : R} {s : S}
    (hs : (algebraMap R S).IsIntegralOverIdeal I s) :
    (algebraMap R S).IsIntegralOverIdeal I (r • s) := sorry
/- Proof strategy: rewrite scalar multiplication as multiplication by
`algebraMap R S r` and use `IsIntegralElem.mul_isIntegralOverIdeal`. -/

/-- Lemma 10.38.3 (Tag 00H4): the elements of an `R`-algebra integral over
`I` form an `R`-submodule. -/
@[stacks 00H4 "submodule of elements integral over an ideal"]
def integralOverIdealSubmodule (I : Ideal R) : Submodule R S where
  carrier := {s | (algebraMap R S).IsIntegralOverIdeal I s}
  zero_mem' := isIntegralOverIdeal_zero (algebraMap R S) I
  add_mem' := fun hx hy ↦ hx.add hy
  smul_mem' := fun _ _ hs ↦ hs.smul

/-- Membership in `integralOverIdealSubmodule I` is integrality over `I`. -/
@[simp, stacks 00H4 "membership in the ideal-integral submodule"]
theorem mem_integralOverIdealSubmodule (I : Ideal R) (s : S) :
    s ∈ integralOverIdealSubmodule I ↔
      (algebraMap R S).IsIntegralOverIdeal I s := sorry
/- Proof strategy: unfold `integralOverIdealSubmodule`. -/

end Algebra

section Map

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- Lemma 10.38.4 (Tag 00H5): under an integral ring homomorphism, every
element of an extended ideal is integral over the source ideal. -/
@[stacks 00H5 "elements of an extended ideal are integral over the ideal"]
theorem isIntegralOverIdeal_of_mem_map {φ : R →+* S} (hφ : φ.IsIntegral)
    {I : Ideal R} {x : S} (hx : x ∈ I.map φ) :
    φ.IsIntegralOverIdeal I x := sorry
/- Proof strategy: install the algebra only inside the eventual proof and apply
`Polynomial.exists_monic_aeval_eq_zero_forall_mem_pow_of_mem_map`. -/

end Map

end RingHom
