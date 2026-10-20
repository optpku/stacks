/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.Topology.Algebra.Algebra
public import Mathlib.Topology.Algebra.IsUniformGroup.Defs
public import Mathlib.Topology.Algebra.LinearTopology
public import Mathlib.Topology.Defs.Induced

/-!
# Restricted power series

Restricted power series over a linearly topologized ring `A` are realized as the inverse limit
of polynomial rings `A ⧸ I` in the variables `σ`, indexed by open ideals `I` of `A`, and equipped
with the inverse-limit topology.
-/

@[expose] public section

universe u v w

noncomputable section

namespace RestrictedPowerSeries

/-- An open ideal of a topological ring, viewed as an index of the inverse system
`I ↦ (A ⧸ I)[σ]`. -/
abbrev OpenIdeal (A : Type v) [CommRing A] [TopologicalSpace A] :=
  { I : Ideal A // IsOpen (I : Set A) }

/-- The underlying set of an open ideal is open. -/
theorem isOpen_coe {A : Type v} [CommRing A] [TopologicalSpace A] (I : OpenIdeal A) :
    IsOpen (I.1 : Set A) :=
  sorry

/-- A family of polynomial reductions is compatible when it is functorial along
inclusions of open ideals. -/
def Compatible {σ : Type u} {A : Type v} [CommRing A] [TopologicalSpace A]
    (f : ∀ I : OpenIdeal A, MvPolynomial σ (A ⧸ I.1)) : Prop :=
  ∀ (I J : OpenIdeal A) (h : I.1 ≤ J.1),
    MvPolynomial.map (Ideal.Quotient.factor h) (f I) = f J

/-- Unfolding of inverse-system compatibility. -/
theorem compatible_iff {σ : Type u} {A : Type v} [CommRing A] [TopologicalSpace A]
    (f : ∀ I : OpenIdeal A, MvPolynomial σ (A ⧸ I.1)) :
    Compatible f ↔
      ∀ (I J : OpenIdeal A) (h : I.1 ≤ J.1),
        MvPolynomial.map (Ideal.Quotient.factor h) (f I) = f J :=
  sorry

namespace Compatible

variable {σ : Type u} {A : Type v} [CommRing A] [TopologicalSpace A]

/-- The zero family of polynomial reductions is compatible. -/
theorem zero : Compatible (0 : ∀ I : OpenIdeal A, MvPolynomial σ (A ⧸ I.1)) := sorry

/-- The unit family of polynomial reductions is compatible. -/
theorem one : Compatible (1 : ∀ I : OpenIdeal A, MvPolynomial σ (A ⧸ I.1)) := sorry

/-- The pointwise sum of compatible polynomial families is compatible. -/
theorem add {f g : ∀ I : OpenIdeal A, MvPolynomial σ (A ⧸ I.1)}
    (hf : Compatible f) (hg : Compatible g) : Compatible (f + g) := sorry

/-- The pointwise negation of a compatible polynomial family is compatible. -/
theorem neg {f : ∀ I : OpenIdeal A, MvPolynomial σ (A ⧸ I.1)}
    (hf : Compatible f) : Compatible (-f) := sorry

/-- The pointwise product of compatible polynomial families is compatible. -/
theorem mul {f g : ∀ I : OpenIdeal A, MvPolynomial σ (A ⧸ I.1)}
    (hf : Compatible f) (hg : Compatible g) : Compatible (f * g) := sorry

/-- Reducing the coefficients of a polynomial modulo every open ideal gives a compatible
family. -/
theorem polynomial (p : MvPolynomial σ A) :
    Compatible (fun I : OpenIdeal A ↦ MvPolynomial.map (Ideal.Quotient.mk I.1) p) := sorry

end Compatible

/-- Compatible polynomial families form a subring of the product of polynomial quotient
rings over all open ideals. -/
def compatibleSubring (σ : Type u) (A : Type v) [CommRing A] [TopologicalSpace A] :
    Subring (∀ I : OpenIdeal A, MvPolynomial σ (A ⧸ I.1)) where
  carrier := Compatible
  zero_mem' := Compatible.zero
  one_mem' := Compatible.one
  add_mem' := Compatible.add
  neg_mem' := Compatible.neg
  mul_mem' := Compatible.mul

end RestrictedPowerSeries

/-- Restricted power series in the variables `σ` over a linearly topologized ring `A`, as the
inverse limit of the discrete polynomial rings `(A ⧸ I)[σ]` over open ideals `I`. For
`σ = Fin r` this is the ring `A{x₁, …, xᵣ}`. -/
def RestrictedPowerSeries (σ : Type u) (A : Type v)
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A] :
    Type (max u v) :=
  { f : ∀ I : RestrictedPowerSeries.OpenIdeal A, MvPolynomial σ (A ⧸ I.1) //
    RestrictedPowerSeries.Compatible f }

namespace RestrictedPowerSeries

variable {σ : Type u} {A : Type v}
variable [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]

/-- Restricted power series form a commutative ring, with componentwise operations. -/
instance instCommRing : CommRing (RestrictedPowerSeries σ A) :=
  fast_instance% (compatibleSubring σ A).toCommRing

/-- The polynomial ring maps to restricted power series by reducing its coefficients
modulo every open ideal. -/
def polynomialRingHom : MvPolynomial σ A →+* RestrictedPowerSeries σ A :=
  (RingHom.pi fun I : OpenIdeal A ↦ MvPolynomial.map (Ideal.Quotient.mk I.1)).codRestrict
    (compatibleSubring σ A) Compatible.polynomial

/-- Coefficient ring acting by constant polynomials in each component. -/
instance instAlgebra : Algebra A (RestrictedPowerSeries σ A) :=
  (polynomialRingHom.comp MvPolynomial.C).toAlgebra

/-- The canonical `A`-algebra map from the polynomial ring into restricted power series,
reducing coefficients modulo each open ideal. -/
def ofPolynomial : MvPolynomial σ A →ₐ[A] RestrictedPowerSeries σ A where
  toRingHom := polynomialRingHom
  commutes' := sorry

/-- Evaluation of a restricted power series at an open ideal, landing in `(A ⧸ I)[σ]`. -/
def component (I : OpenIdeal A) : RestrictedPowerSeries σ A →+* MvPolynomial σ (A ⧸ I.1) :=
  (Pi.evalRingHom (fun J : OpenIdeal A ↦ MvPolynomial σ (A ⧸ J.1)) I).comp
    (compatibleSubring σ A).subtype

/-- Inverse-limit topology: the infimum of the discrete topologies on the polynomial
components `(A ⧸ I)[σ]`. -/
instance instTopologicalSpace : TopologicalSpace (RestrictedPowerSeries σ A) :=
  ⨅ I : OpenIdeal A,
    TopologicalSpace.induced (fun f : RestrictedPowerSeries σ A ↦ f.1 I)
      (⊥ : TopologicalSpace (MvPolynomial σ (A ⧸ I.1)))

/-- Restricted power series form a topological ring. -/
instance instIsTopologicalRing : IsTopologicalRing (RestrictedPowerSeries σ A) :=
  sorry

/-- The inverse-limit topology on restricted power series is linear. -/
instance instIsLinearTopology :
    IsLinearTopology (RestrictedPowerSeries σ A) (RestrictedPowerSeries σ A) :=
  sorry

/-- Restricted power series are Hausdorff. -/
instance instT2Space : T2Space (RestrictedPowerSeries σ A) :=
  sorry

/-- Restricted power series are complete for the additive right uniformity. -/
instance instCompleteSpace :
    @CompleteSpace (RestrictedPowerSeries σ A)
      (IsTopologicalAddGroup.rightUniformSpace (RestrictedPowerSeries σ A)) :=
  sorry

/-- Scalar multiplication by coefficients is continuous on restricted power series. -/
instance instContinuousSMul : ContinuousSMul A (RestrictedPowerSeries σ A) :=
  sorry

/-- Extensionality of restricted power series by their open-ideal components. -/
theorem ext {f g : RestrictedPowerSeries σ A}
    (h : ∀ I : OpenIdeal A, component I f = component I g) : f = g :=
  sorry

/-- Componentwise evaluation of a restricted power series. -/
theorem component_apply (I : OpenIdeal A) (f : RestrictedPowerSeries σ A) :
    component I f = f.1 I :=
  sorry

/-- The canonical polynomial map reduces coefficients modulo each open ideal. -/
theorem ofPolynomial_apply (p : MvPolynomial σ A) (I : OpenIdeal A) :
    component I (ofPolynomial p) = MvPolynomial.map (Ideal.Quotient.mk I.1) p :=
  sorry

/-- Constants are sent to the algebra map of restricted power series. -/
theorem ofPolynomial_C (a : A) :
    ofPolynomial (MvPolynomial.C a) = algebraMap A (RestrictedPowerSeries σ A) a :=
  sorry

/-- Indeterminates remain indeterminates in every polynomial component. -/
theorem ofPolynomial_X (i : σ) (I : OpenIdeal A) :
    component I (ofPolynomial (MvPolynomial.X i)) = MvPolynomial.X i :=
  sorry

/-- A continuous coefficient map between complete Hausdorff linearly topologized rings
allows every finite-variable polynomial algebra map to extend uniquely and continuously
to restricted power series. -/
theorem existsUnique_continuousAlgHom
    {r : ℕ} {C : Type w}
    [T2Space A]
    [@CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A)]
    [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsLinearTopology C C] [T2Space C]
    [@CompleteSpace C (IsTopologicalAddGroup.rightUniformSpace C)] [Algebra A C]
    (hAC : Continuous (algebraMap A C)) (φ : MvPolynomial (Fin r) A →ₐ[A] C) :
    ∃! ψ : RestrictedPowerSeries (Fin r) A →A[A] C,
      ψ.toAlgHom.comp ofPolynomial = φ :=
  sorry

end RestrictedPowerSeries
