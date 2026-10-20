/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Polynomial.Derivation
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.LinearAlgebra.Basis.Basic

@[expose] public section

open Module Polynomial

universe u v w

namespace PurelyInseparableTrace

/-- Polynomial differentiation descends through the quotient by `X ^ p - C a` in
characteristic `p`. -/
theorem derivative_respects_pPowerRelation (p : ℕ) (hp : p.Prime)
    (R : Type u) [CommRing R] [Algebra (ZMod p) R] (a : R) (f : R[X])
    (hf : AdjoinRoot.mk (X ^ p - C a) f = 0) :
    AdjoinRoot.mk (X ^ p - C a) (derivative f) = 0 := sorry

/-- The derivation of `R[x]/(x ^ p - a)` that sends the distinguished root to `1`. -/
noncomputable def rootDerivation (p : ℕ) (hp : p.Prime)
    (R : Type u) [CommRing R] [Algebra (ZMod p) R] (a : R) :
    Derivation R (AdjoinRoot (X ^ p - C a)) (AdjoinRoot (X ^ p - C a)) :=
  Polynomial.derivative'.liftOfSurjective
    (f := AdjoinRoot.mkₐ (X ^ p - C a)) AdjoinRoot.mk_surjective
    (derivative_respects_pPowerRelation p hp R a)

/-- The distinguished-root value of `rootDerivation` is `1`. -/
theorem rootDerivation_root (p : ℕ) (hp : p.Prime)
    (R : Type u) [CommRing R] [Algebra (ZMod p) R] (a : R) :
    rootDerivation p hp R a (AdjoinRoot.root (X ^ p - C a)) = 1 := sorry

/-- The forward coordinate map sends a relative differential to its coefficient of the
distinguished-root differential. -/
noncomputable def differentialForward (p : ℕ) (hp : p.Prime)
    (R : Type u) [CommRing R] [Algebra (ZMod p) R] (a : R) :
    KaehlerDifferential R (AdjoinRoot (X ^ p - C a)) →ₗ[AdjoinRoot (X ^ p - C a)]
      AdjoinRoot (X ^ p - C a) :=
  (rootDerivation p hp R a).liftKaehlerDifferential

/-- The forward coordinate map sends `dx` to `1`. -/
theorem differentialForward_D_root (p : ℕ) (hp : p.Prime)
    (R : Type u) [CommRing R] [Algebra (ZMod p) R] (a : R) :
    differentialForward p hp R a
        (KaehlerDifferential.D R (AdjoinRoot (X ^ p - C a))
          (AdjoinRoot.root (X ^ p - C a))) = 1 := sorry

/-- The inverse coordinate map sends `s` to `s • dx`. -/
noncomputable def differentialInverse (p : ℕ) (R : Type u)
    [CommRing R] [Algebra (ZMod p) R] (a : R) :
    AdjoinRoot (X ^ p - C a) →ₗ[AdjoinRoot (X ^ p - C a)]
      KaehlerDifferential R (AdjoinRoot (X ^ p - C a)) :=
  (Algebra.lsmul (AdjoinRoot (X ^ p - C a)) (AdjoinRoot (X ^ p - C a)) _).toLinearMap.flip
    (KaehlerDifferential.D R (AdjoinRoot (X ^ p - C a))
      (AdjoinRoot.root (X ^ p - C a)))

/-- The inverse coordinate map has the formula `s ↦ s • dx`. -/
theorem differentialInverse_apply (p : ℕ) (R : Type u)
    [CommRing R] [Algebra (ZMod p) R] (a : R) (s : AdjoinRoot (X ^ p - C a)) :
    differentialInverse p R a s = s •
      KaehlerDifferential.D R (AdjoinRoot (X ^ p - C a))
        (AdjoinRoot.root (X ^ p - C a)) := sorry

/-- The explicit inverse coordinate map is a left inverse to the forward map. -/
theorem differentialInverse_forward (p : ℕ) (hp : p.Prime)
    (R : Type u) [CommRing R] [Algebra (ZMod p) R] (a : R)
    (ω : KaehlerDifferential R (AdjoinRoot (X ^ p - C a))) :
    differentialInverse p R a (differentialForward p hp R a ω) = ω := sorry

/-- The explicit inverse coordinate map is a right inverse to the forward map. -/
theorem differentialForward_inverse (p : ℕ) (hp : p.Prime)
    (R : Type u) [CommRing R] [Algebra (ZMod p) R] (a : R)
    (s : AdjoinRoot (X ^ p - C a)) :
    differentialForward p hp R a (differentialInverse p R a s) = s := sorry

/-- The explicit equivalence identifying relative differentials with the quotient algebra by the
coefficient of `dx`. -/
noncomputable def differentialEquiv (p : ℕ) (hp : p.Prime)
    (R : Type u) [CommRing R] [Algebra (ZMod p) R] (a : R) :
    KaehlerDifferential R (AdjoinRoot (X ^ p - C a)) ≃ₗ[AdjoinRoot (X ^ p - C a)]
      AdjoinRoot (X ^ p - C a) where
  __ := differentialForward p hp R a
  invFun := differentialInverse p R a
  left_inv := differentialInverse_forward p hp R a
  right_inv := differentialForward_inverse p hp R a

/-- The forward map of `differentialEquiv` is `differentialForward`. -/
theorem differentialEquiv_apply (p : ℕ) (hp : p.Prime)
    (R : Type u) [CommRing R] [Algebra (ZMod p) R] (a : R)
    (ω : KaehlerDifferential R (AdjoinRoot (X ^ p - C a))) :
    differentialEquiv p hp R a ω = differentialForward p hp R a ω := sorry

/-- The canonical `R`-basis `x ^ i • dx`, `0 ≤ i < p`, of the relative Kähler
differentials of `R[x]/(x ^ p - a)`. -/
noncomputable def differentialBasis (p : ℕ) (hp : p.Prime)
    (R : Type u) [CommRing R] [Algebra (ZMod p) R] (a : R) :
    Basis (Fin p) R (KaehlerDifferential R (AdjoinRoot (X ^ p - C a))) :=
  -- Local instance justification (proof-local temporary data): the decidable `Nontrivial R` instance is used only to choose the branch-specific basis construction.
  letI := Classical.dec (Nontrivial R)
  if hR : Nontrivial R then
    -- Local instance justification (proof-local temporary data): `hR` is installed only within the nontrivial branch for the required power-basis construction.
    letI := hR
    Basis.map
      ((AdjoinRoot.powerBasis' (monic_X_pow_sub_C a hp.ne_zero)).basis.reindex
        (finCongr natDegree_X_pow_sub_C))
      ((differentialEquiv p hp R a).symm.restrictScalars R)
  else
    -- Local instance justification (proof-local temporary data): the subsingleton instance is installed only in the complementary branch to construct the default basis.
    letI : Subsingleton R := not_nontrivial_iff_subsingleton.mp hR
    default

/-- The `i`th vector of `differentialBasis` is `x ^ i • dx`. -/
theorem differentialBasis_apply (p : ℕ) (hp : p.Prime)
    (R : Type u) [CommRing R] [Algebra (ZMod p) R] (a : R) (i : Fin p) :
    differentialBasis p hp R a i =
      AdjoinRoot.root (X ^ p - C a) ^ (i : ℕ) •
        KaehlerDifferential.D R (AdjoinRoot (X ^ p - C a))
          (AdjoinRoot.root (X ^ p - C a)) := sorry

/-- The positive-characteristic trace map on differentials for
`R[x]/(x ^ p - a)`: it extracts the coefficient of `x ^ (p - 1) • dx` and
multiplies it by `da`. -/
noncomputable def trace (p : ℕ) (hp : p.Prime)
    (R : Type u) [CommRing R] [Algebra (ZMod p) R] (a : R) :
    KaehlerDifferential R (AdjoinRoot (X ^ p - C a)) →ₗ[R]
      KaehlerDifferential (ZMod p) R :=
  ((differentialBasis p hp R a).coord
      ⟨p - 1, Nat.sub_lt hp.pos Nat.one_pos⟩).smulRight
    (KaehlerDifferential.D (ZMod p) R a)

/-- The trace sends `x ^ i • dx` to `da` in degree `p - 1` and to zero otherwise. -/
theorem trace_apply_rootPowD (p : ℕ) (hp : p.Prime)
    (R : Type u) [CommRing R] [Algebra (ZMod p) R] (a : R) (i : Fin p) :
    trace p hp R a
        (AdjoinRoot.root (X ^ p - C a) ^ (i : ℕ) •
          KaehlerDifferential.D R (AdjoinRoot (X ^ p - C a))
            (AdjoinRoot.root (X ^ p - C a))) =
      if (i : ℕ) = p - 1 then KaehlerDifferential.D (ZMod p) R a else 0 := sorry

/-- The map on relative Kähler differentials induced by an `R`-algebra homomorphism. -/
noncomputable def mapOfAlgHom {R : Type u} {A : Type v} {B : Type w}
    [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (φ : A →ₐ[R] B) : KaehlerDifferential R A →ₗ[R] KaehlerDifferential R B :=
  -- Local instance justification (noncanonical choice): `φ` selects the `A`-algebra structure on `B`, while distinct `R`-algebra maps can induce competing choices.
  letI : Algebra A B := φ.toRingHom.toAlgebra
  -- Local instance justification (instance diamond): this tower proof belongs to the `A`-algebra structure selected by `φ`, so a global instance could select another map.
  letI : IsScalarTower R A B :=
    IsScalarTower.of_algebraMap_eq fun r ↦ (φ.commutes r).symm
  (KaehlerDifferential.map R R A B).restrictScalars R

/-- The induced map on relative Kähler differentials sends `dz` to `d(φ z)`. -/
theorem mapOfAlgHom_D {R : Type u} {A : Type v} {B : Type w}
    [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (φ : A →ₐ[R] B) (z : A) :
    mapOfAlgHom φ (KaehlerDifferential.D R A z) =
      KaehlerDifferential.D R B (φ z) := sorry

/-- An `R`-algebra homomorphism between the quotients by `X ^ p - C a` and
`X ^ p - C b` intertwines their positive-characteristic trace maps on relative
Kähler differentials. -/
theorem pPowerTrace_natural (p : ℕ) (hp : p.Prime)
    (R : Type u) [CommRing R] [Algebra (ZMod p) R] (a b : R)
    (φ : AdjoinRoot (X ^ p - C a) →ₐ[R] AdjoinRoot (X ^ p - C b)) :
    trace p hp R a = (trace p hp R b).comp (mapOfAlgHom φ) := sorry

end PurelyInseparableTrace
