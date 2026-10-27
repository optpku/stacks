/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import ReasLib.NumberTheory.Padics.Localization
public import ReasLib.RingTheory.DividedPowers.Padic
public import ReasLib.RingTheory.DividedPowers.Prime.Characterization
public import ReasLib.RingTheory.DividedPowers.Thickening

@[expose] public section

noncomputable section

open DividedPowers Function

namespace Crystalline.SquaredOrigin

/-- Coordinates on `𝔽_p[x, y] / (x², xy, y²)`. -/
inductive Coord where
  | x
  | y
  deriving DecidableEq

/-- Coordinates on the witness algebra `B`, including the kernel generators `u` and `v`. -/
inductive WitnessVar where
  | x
  | y
  | u
  | v
  deriving DecidableEq

/-- The ideal `(x², xy, y²)` in `𝔽_p[x, y]`. -/
def coordinateIdeal (p : ℕ) [Fact p.Prime] : Ideal (MvPolynomial Coord (ZMod p)) :=
  Ideal.span
    ({MvPolynomial.X Coord.x ^ 2,
      MvPolynomial.X Coord.x * MvPolynomial.X Coord.y,
      MvPolynomial.X Coord.y ^ 2} : Set (MvPolynomial Coord (ZMod p)))

/-- The coordinate ring `C = 𝔽_p[x, y] / (x², xy, y²)`. -/
abbrev coordinateRing (p : ℕ) [Fact p.Prime] : Type :=
  MvPolynomial Coord (ZMod p) ⧸ coordinateIdeal p

/-- The polynomial ring `P = ℤ_[p][x, y]`. -/
abbrev polynomialRing (p : ℕ) [Fact p.Prime] : Type :=
  MvPolynomial Coord ℤ_[p]

/-- The divided-power ideal `(p) ⊂ ℤ_[p]`. -/
abbrev padicIdeal (p : ℕ) [Fact p.Prime] : Ideal ℤ_[p] :=
  Ideal.span {(p : ℤ_[p])}

/-- The presentation ideal `J = (x², xy, y², p) ⊂ P`. -/
def presentationIdeal (p : ℕ) [Fact p.Prime] : Ideal (polynomialRing p) :=
  Ideal.span
    ({MvPolynomial.X Coord.x ^ 2,
      MvPolynomial.X Coord.x * MvPolynomial.X Coord.y,
      MvPolynomial.X Coord.y ^ 2,
      (p : polynomialRing p)} : Set (polynomialRing p))

/-- The presentation `P → C`, reducing coefficients modulo `p` and quotienting by `(x², xy, y²)`. -/
def presentation (p : ℕ) [Fact p.Prime] : polynomialRing p →ₐ[ℤ_[p]] coordinateRing p :=
  (Ideal.Quotient.mkₐ ℤ_[p] (coordinateIdeal p)).comp
    (MvPolynomial.mapAlgHom (Algebra.ofId ℤ_[p] (ZMod p)))

/-- The presentation sends a coordinate to its image in `C`. -/
theorem presentation_X (p : ℕ) [Fact p.Prime] (i : Coord) :
    presentation p (MvPolynomial.X i) =
      Ideal.Quotient.mk (coordinateIdeal p) (MvPolynomial.X i) := sorry

/-- The presentation `P → C` is surjective. -/
theorem presentation_surjective (p : ℕ) [Fact p.Prime] :
    Function.Surjective (presentation p) := sorry

/-- The kernel of the presentation is `J = (x², xy, y², p)`. -/
theorem ker_presentation (p : ℕ) [Fact p.Prime] :
    RingHom.ker (presentation p).toRingHom = presentationIdeal p := sorry

/-- The image of `(p) ⊂ ℤ_[p]` lies in `J`. -/
theorem primeMap_le (p : ℕ) [Fact p.Prime] :
    Ideal.map (algebraMap ℤ_[p] (polynomialRing p)) (padicIdeal p) ≤ presentationIdeal p := sorry

/-- The integer `p` is nilpotent on `C`. -/
theorem coordinate_p_nilpotent (p : ℕ) [Fact p.Prime] :
    IsNilpotent (p : coordinateRing p) := sorry

/-- The image of `(p)` in `C` is zero. -/
theorem coordinate_prime_bot (p : ℕ) [Fact p.Prime] :
    Ideal.map (algebraMap ℤ_[p] (coordinateRing p)) (padicIdeal p) =
      (⊥ : Ideal (coordinateRing p)) := sorry

/-- The ideal of relations defining the witness ring `B`. `uv` is not a relation. -/
def witnessIdeal (p : ℕ) [Fact p.Prime] : Ideal (MvPolynomial WitnessVar (ZMod p)) :=
  Ideal.span
    ({MvPolynomial.X WitnessVar.x ^ 3,
      MvPolynomial.X WitnessVar.x ^ 2 * MvPolynomial.X WitnessVar.y,
      MvPolynomial.X WitnessVar.x * MvPolynomial.X WitnessVar.y ^ 2,
      MvPolynomial.X WitnessVar.y ^ 3,
      MvPolynomial.X WitnessVar.x * MvPolynomial.X WitnessVar.u,
      MvPolynomial.X WitnessVar.y * MvPolynomial.X WitnessVar.u,
      MvPolynomial.X WitnessVar.x * MvPolynomial.X WitnessVar.v,
      MvPolynomial.X WitnessVar.y * MvPolynomial.X WitnessVar.v,
      MvPolynomial.X WitnessVar.u ^ 2,
      MvPolynomial.X WitnessVar.v ^ 2} : Set (MvPolynomial WitnessVar (ZMod p)))

/-- The witness ring `B = 𝔽_p[x, y, u, v] / (x³, x²y, xy², y³, xu, yu, xv, yv, u², v²)`. -/
abbrev witnessRing (p : ℕ) [Fact p.Prime] : Type :=
  MvPolynomial WitnessVar (ZMod p) ⧸ witnessIdeal p

/-- The image of a witness coordinate in `B`. -/
def witnessGen (p : ℕ) [Fact p.Prime] (i : WitnessVar) : witnessRing p :=
  Ideal.Quotient.mk (witnessIdeal p) (MvPolynomial.X i)

/-- The product `uv` in `B`. -/
def witnessUv (p : ℕ) [Fact p.Prime] : witnessRing p :=
  witnessGen p WitnessVar.u * witnessGen p WitnessVar.v

/-- The class of `uv` is nonzero in `B`. -/
theorem witnessUv_ne_zero (p : ℕ) [Fact p.Prime] : witnessUv p ≠ 0 := sorry

/-- Images of the witness variables in `C`: `x` and `y` are preserved and `u`, `v` go to zero. -/
def witnessVarImage (p : ℕ) [Fact p.Prime] : WitnessVar → coordinateRing p
  | WitnessVar.x => Ideal.Quotient.mk (coordinateIdeal p) (MvPolynomial.X Coord.x)
  | WitnessVar.y => Ideal.Quotient.mk (coordinateIdeal p) (MvPolynomial.X Coord.y)
  | WitnessVar.u => 0
  | WitnessVar.v => 0

/-- The polynomial-level map `𝔽_p[x, y, u, v] → C` before quotienting by the relations of `B`. -/
def witnessPolynomialToCoordinate (p : ℕ) [Fact p.Prime] :
    MvPolynomial WitnessVar (ZMod p) →ₐ[ZMod p] coordinateRing p :=
  MvPolynomial.aeval (witnessVarImage p)

/-- On variables, `witnessPolynomialToCoordinate` is `witnessVarImage`. -/
theorem witnessPolynomialToCoordinate_X (p : ℕ) [Fact p.Prime] (i : WitnessVar) :
    witnessPolynomialToCoordinate p (MvPolynomial.X i) = witnessVarImage p i := sorry

/-- The kernel condition needed to descend `witnessPolynomialToCoordinate` to `B`. -/
theorem witnessPolynomialToCoordinate_mem_ideal (p : ℕ) [Fact p.Prime]
    (a : MvPolynomial WitnessVar (ZMod p)) (ha : a ∈ witnessIdeal p) :
    witnessPolynomialToCoordinate p a = 0 := sorry

/-- The surjection `B → C` sending `x, y` to themselves and `u, v` to zero. -/
def witnessToCoordinate (p : ℕ) [Fact p.Prime] : witnessRing p →+* coordinateRing p :=
  Ideal.Quotient.lift (witnessIdeal p) (witnessPolynomialToCoordinate p).toRingHom
    (witnessPolynomialToCoordinate_mem_ideal p)

/-- `witnessToCoordinate` descends `witnessPolynomialToCoordinate`. -/
theorem witnessToCoordinate_mk (p : ℕ) [Fact p.Prime]
    (f : MvPolynomial WitnessVar (ZMod p)) :
    witnessToCoordinate p (Ideal.Quotient.mk (witnessIdeal p) f) =
      witnessPolynomialToCoordinate p f := sorry

/-- The surjection `B → C` is surjective. -/
theorem witnessToCoordinate_surjective (p : ℕ) [Fact p.Prime] :
    Function.Surjective (witnessToCoordinate p) := sorry

/-- Inclusion of the two polynomial coordinates into the four witness variables. -/
def coordToWitness : Coord → WitnessVar
  | Coord.x => WitnessVar.x
  | Coord.y => WitnessVar.y

/-- The obvious map `P → B`, reducing coefficients modulo `p` and sending `x, y` to themselves. -/
def polynomialToWitness (p : ℕ) [Fact p.Prime] : polynomialRing p →+* witnessRing p :=
  (Ideal.Quotient.mk (witnessIdeal p)).comp
    ((MvPolynomial.rename coordToWitness).toRingHom.comp
      (MvPolynomial.map PadicInt.toZMod))

/-- `polynomialToWitness` sends a coordinate to its class in `B`. -/
theorem polynomialToWitness_X (p : ℕ) [Fact p.Prime] (i : Coord) :
    polynomialToWitness p (MvPolynomial.X i) = witnessGen p (coordToWitness i) := sorry

/-- The prime operation on representatives reads the quadratic coefficients and, at `p = 2`,
adds the product of the linear `u` and `v` coefficients times `uv`. -/
def preDpow (p : ℕ) [Fact p.Prime]
    (f : MvPolynomial WitnessVar (ZMod p)) : MvPolynomial WitnessVar (ZMod p) :=
  MvPolynomial.C ((f.coeff (Finsupp.single WitnessVar.x 2)) ^ p) * MvPolynomial.X WitnessVar.u +
    MvPolynomial.C ((f.coeff (Finsupp.single WitnessVar.y 2)) ^ p) * MvPolynomial.X WitnessVar.v +
    if p = 2 then
      MvPolynomial.C (f.coeff (Finsupp.single WitnessVar.u 1) *
        f.coeff (Finsupp.single WitnessVar.v 1)) *
          MvPolynomial.X WitnessVar.u * MvPolynomial.X WitnessVar.v
    else 0

/-- The prime operation on polynomial representatives is independent of representatives
modulo the witness ideal. -/
theorem preDpow_quotient_eq (p : ℕ) [Fact p.Prime]
    (f g : MvPolynomial WitnessVar (ZMod p))
    (hfg : Ideal.Quotient.mk (witnessIdeal p) f = Ideal.Quotient.mk (witnessIdeal p) g) :
    Ideal.Quotient.mk (witnessIdeal p) (preDpow p f) =
      Ideal.Quotient.mk (witnessIdeal p) (preDpow p g) := sorry

/-- The image of `preDpow` of a kernel representative remains in `ker(B → C)`. -/
theorem preDpow_mem_ker (p : ℕ) [Fact p.Prime]
    (z : RingHom.ker (witnessToCoordinate p)) :
    Ideal.Quotient.mk (witnessIdeal p)
        (preDpow p (Quotient.out (z : witnessRing p))) ∈
      RingHom.ker (witnessToCoordinate p) := sorry

/-- The prime divided-power operation `δ_p` on `K = ker(B → C)`. -/
def witnessDpowPrime (p : ℕ) [Fact p.Prime]
    (z : RingHom.ker (witnessToCoordinate p)) : RingHom.ker (witnessToCoordinate p) :=
  ⟨Ideal.Quotient.mk (witnessIdeal p)
      (preDpow p (Quotient.out (z : witnessRing p))),
    preDpow_mem_ker p z⟩

/-- On `ax² + bxy + cy² + du + ev + fuv`, the prime operation is
`a^p u + c^p v`, with the additional term `de uv` exactly when `p = 2`. -/
theorem witnessDpowPrime_normalForm (p : ℕ) [Fact p.Prime]
    (a b c d e f : ZMod p) (z : RingHom.ker (witnessToCoordinate p))
    (hz : (z : witnessRing p) =
      Ideal.Quotient.mk (witnessIdeal p)
        (MvPolynomial.C a * MvPolynomial.X WitnessVar.x ^ 2 +
          MvPolynomial.C b * MvPolynomial.X WitnessVar.x * MvPolynomial.X WitnessVar.y +
          MvPolynomial.C c * MvPolynomial.X WitnessVar.y ^ 2 +
          MvPolynomial.C d * MvPolynomial.X WitnessVar.u +
          MvPolynomial.C e * MvPolynomial.X WitnessVar.v +
          MvPolynomial.C f * MvPolynomial.X WitnessVar.u * MvPolynomial.X WitnessVar.v)) :
    (witnessDpowPrime p z : witnessRing p) =
      Ideal.Quotient.mk (witnessIdeal p)
        (MvPolynomial.C (a ^ p) * MvPolynomial.X WitnessVar.u +
          MvPolynomial.C (c ^ p) * MvPolynomial.X WitnessVar.v +
          if p = 2 then MvPolynomial.C (d * e) *
            MvPolynomial.X WitnessVar.u * MvPolynomial.X WitnessVar.v else 0) := sorry

/-- The corrected prime operation satisfies the factorial, scalar, and addition identities
for a prime divided-power operation. -/
theorem witnessDpowPrime_isDpowPrime (p : ℕ) [Fact p.Prime] :
    (witnessDpowPrime p).IsDpowPrime p := sorry

/-- Integers not divisible by `p` are units in `B`. -/
theorem witness_primeToP_isUnit (p : ℕ) [Fact p.Prime] (n : ℕ) (hn : ¬ p ∣ n) :
    IsUnit (n : witnessRing p) := sorry

/-- The endomorphism of `P` induced by `x ↦ x^p` and `y ↦ y^p`, fixing `ℤ_[p]`. -/
def polynomialFrobenius (p : ℕ) [Fact p.Prime] :
    polynomialRing p →ₐ[ℤ_[p]] polynomialRing p :=
  MvPolynomial.aeval fun i : Coord ↦ MvPolynomial.X i ^ p

/-- `polynomialFrobenius` raises coordinates to the `p`th power. -/
theorem polynomialFrobenius_X (p : ℕ) [Fact p.Prime] (i : Coord) :
    polynomialFrobenius p (MvPolynomial.X i) = MvPolynomial.X i ^ p := sorry

/-- The witness ring as a divided-power ring on `ker(B → C)`. -/
def witnessDPRing (p : ℕ) [Fact p.Prime]
    (δ : DividedPowers (RingHom.ker (witnessToCoordinate p))) :
    DividedPowerRing :=
  DividedPowerRing.of (witnessRing p) (RingHom.ker (witnessToCoordinate p)) δ

/-- `p` is nilpotent on the witness ring. -/
theorem witness_p_nilpotent (p : ℕ) [Fact p.Prime] :
    IsNilpotent (p : witnessRing p) := sorry

/-- The algebra map `ℤ_[p] → B` is a divided-power morphism onto `δ`. -/
theorem witnessBase_isDPMorphism (p : ℕ) [Fact p.Prime]
    (δ : DividedPowers (RingHom.ker (witnessToCoordinate p)))
    (hδ : δ.dpowPrime p = witnessDpowPrime p) :
    IsDPMorphism (PadicInt.dividedPowers p) δ (algebraMap ℤ_[p] (witnessRing p)) := sorry

/-- The first-isomorphism inverse `C → B / ker(B → C)`. -/
def witnessQuotient (p : ℕ) [Fact p.Prime] :
    coordinateRing p →+* witnessRing p ⧸ RingHom.ker (witnessToCoordinate p) :=
  (RingHom.quotientKerEquivOfSurjective (witnessToCoordinate_surjective p)).symm.toRingHom

/-- The square relating `ℤ_[p] → B` and `ℤ_[p] → C` after quotienting by `ker(B → C)`. -/
theorem witnessQuotient_commutative (p : ℕ) [Fact p.Prime] :
    (Ideal.Quotient.mk (RingHom.ker (witnessToCoordinate p))).comp
        (algebraMap ℤ_[p] (witnessRing p)) =
      (witnessQuotient p).comp (algebraMap ℤ_[p] (coordinateRing p)) := sorry

/-- The object `(B → C, δ)` of `Cris(C / Spec(ℤ_[p]))`. -/
def witnessThickening (p : ℕ) [Fact p.Prime]
    (δ : DividedPowers (RingHom.ker (witnessToCoordinate p)))
    (hδ : δ.dpowPrime p = witnessDpowPrime p) :
    DividedPowerThickening p ℤ_[p] (padicIdeal p) (PadicInt.dividedPowers p)
      (coordinateRing p) (algebraMap ℤ_[p] (coordinateRing p))
      (coordinate_prime_bot p) (coordinate_p_nilpotent p) :=
  DividedPowerThickening.of (PadicInt.dividedPowers p)
    (algebraMap ℤ_[p] (coordinateRing p)) (coordinate_prime_bot p)
    (coordinate_p_nilpotent p) (witnessDPRing p δ)
    (DPMorphism.mk' (witnessBase_isDPMorphism p δ hδ))
    (witness_p_nilpotent p) (witnessQuotient p)
    (witnessQuotient_commutative p)

/-- The underlying map of the witness thickening is `algebraMap ℤ_[p] B`. -/
theorem witnessThickening_toRingHom (p : ℕ) [Fact p.Prime]
    (δ : DividedPowers (RingHom.ker (witnessToCoordinate p)))
    (hδ : δ.dpowPrime p = witnessDpowPrime p) :
    (witnessThickening p δ hδ).base.toRingHom = algebraMap ℤ_[p] (witnessRing p) := sorry

end Crystalline.SquaredOrigin
