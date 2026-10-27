/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import ReasLib.AlgebraicGeometry.Crystalline.Cech.Polynomial
public import ReasLib.RingTheory.DividedPowers.Envelope.Completion
public import ReasLib.RingTheory.DividedPowers.Envelope.Universal

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Crystalline
open AlgebraicGeometry.Scheme.Modules
open CrystallineModuleSheaf
open CechCrisCover
open DividedPowers.PAdic

universe u

section EnvelopeData

variable (p : ℕ) [Fact (Nat.Prime p)]
variable {A : Type u} [CommRing A]
variable [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
variable (IA : Ideal A) (γA : DividedPowers IA)
variable {I : (Spec.{u} (.of A)).IdealSheafData}
variable {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
variable (c : CechCrisCover x₀)

/-- Envelope data on each simplex of a Čech crystalline covering. -/
structure CechCrisEnvelope where
  /-- Well-definedness of each simplex envelope. -/
  hIJ : ∀ n σ,
    Ideal.map (algebraMap A (c.simplexPolynomial n σ)) IA ≤ c.simplexKernel n σ
  /-- Chosen divided-power envelopes of the simplex kernels. -/
  E : ∀ n σ,
    DividedPowerEnvelope IA γA (algebraMap A (c.simplexPolynomial n σ))
      (c.simplexKernel n σ) (hIJ n σ)
  /-- Exponents witnessing that a power of `p` lies in the envelope ideal. -/
  N : ∀ (n : ℕ) (_ : Fin (n + 1) → c.Λ), ℕ
  /-- Membership of the chosen `p`-power in the envelope ideal. -/
  hN : ∀ n σ, Ideal.span {(p : (E n σ).D)} ^ N n σ ≤ (E n σ).D.ideal
  /-- Universality of each chosen simplex envelope. -/
  hE : ∀ n σ, DividedPowerEnvelope.IsUniversal γA
    (algebraMap A (c.simplexPolynomial n σ)) (hIJ n σ) (E n σ)

namespace CechCrisEnvelope

/-- Assemble simplex envelope data from well-defined universal envelopes. -/
def ofFamily
    (hIJ : ∀ n σ,
      Ideal.map (algebraMap A (c.simplexPolynomial n σ)) IA ≤ c.simplexKernel n σ)
    (E : ∀ n σ,
      DividedPowerEnvelope IA γA (algebraMap A (c.simplexPolynomial n σ))
        (c.simplexKernel n σ) (hIJ n σ))
    (N : ∀ (n : ℕ) (_ : Fin (n + 1) → c.Λ), ℕ)
    (hN : ∀ n σ, Ideal.span {(p : (E n σ).D)} ^ N n σ ≤ (E n σ).D.ideal)
    (hE : ∀ n σ, DividedPowerEnvelope.IsUniversal γA
      (algebraMap A (c.simplexPolynomial n σ)) (hIJ n σ) (E n σ)) :
    CechCrisEnvelope p IA γA c :=
  { hIJ, E, N, hN, hE }

/-- Every simplex envelope contains the base ideal, contains the chosen power of `p`,
and satisfies the universal mapping property for its polynomial kernel. -/
theorem spec (E : CechCrisEnvelope p IA γA c) (n : ℕ) (σ : Fin (n + 1) → c.Λ) :
    (Ideal.map (algebraMap A (c.simplexPolynomial n σ)) IA ≤ c.simplexKernel n σ) ∧
      (Ideal.span {(p : (E.E n σ).D)} ^ E.N n σ ≤ (E.E n σ).D.ideal) ∧
      DividedPowerEnvelope.IsUniversal γA (algebraMap A (c.simplexPolynomial n σ))
        (E.hIJ n σ) (E.E n σ) := sorry

end CechCrisEnvelope

end EnvelopeData

section EnvelopeMaps

variable {p : ℕ} [Fact (Nat.Prime p)]
variable {A : Type u} [CommRing A]
variable [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
variable {IA : Ideal A} {γA : DividedPowers IA}
variable {I : (Spec.{u} (.of A)).IdealSheafData}
variable {γS : ∀ V : (Spec.{u} (.of A)).affineOpens, DividedPowers (I.ideal V)}
variable {h_compatible :
    ∀ (V : (Spec.{u} (.of A)).affineOpens) (f : Γ(Spec (.of A), V)),
      (γS V).IsDPMorphism (γS ((Spec (.of A)).affineBasicOpen f))
        ((Spec (.of A)).presheaf.map
          (homOfLE ((Spec (.of A)).basicOpen_le f)).op).hom}
variable {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
variable {c : CechCrisCover x₀}

namespace CechCrisEnvelope

/-- Reindexing of finite tuples along a simplex operator. -/
def reindex {n m : SimplexCategory} (f : n ⟶ m)
    (σ : Fin (m.len + 1) → c.Λ) : Fin (n.len + 1) → c.Λ :=
  fun i => σ (SimplexCategory.Hom.toOrderHom f i)

/-- Reindexing applies the order homomorphism of a simplex operator. -/
theorem reindex_apply {n m : SimplexCategory} (f : n ⟶ m)
    (σ : Fin (m.len + 1) → c.Λ) (i : Fin (n.len + 1)) :
    reindex f σ i = σ (SimplexCategory.Hom.toOrderHom f i) :=
  rfl

variable (E : CechCrisEnvelope p IA γA c)

/-- Canonical divided powers on the `p`-adic completion of a simplex envelope. -/
noncomputable def γhat (n : ℕ) (σ : Fin (n + 1) → c.Λ) :
    DividedPowers (RingHom.ker
      (AdicCompletion.toQuotient (Ideal.span {(p : (E.E n σ).D)})
        (E.E n σ).D.ideal (E.N n σ) (E.hN n σ))) :=
  envelopeCompletionDividedPowers (E.E n σ) (E.N n σ) (E.hN n σ)

/-- The completed divided powers are the canonical ones. -/
theorem γhat_eq (n : ℕ) (σ : Fin (n + 1) → c.Λ) :
    E.γhat n σ = envelopeCompletionDividedPowers (E.E n σ) (E.N n σ) (E.hN n σ) :=
  rfl

/-- The polynomial comparison into a target envelope preserves divided powers on `IA`. -/
theorem simplexPolynomialMap_toEnvelope_isDPMorphism
    {n m : SimplexCategory} (f : n ⟶ m) (σ : Fin (m.len + 1) → c.Λ) :
    DividedPowers.IsDPMorphism γA (E.E m.len σ).D.dividedPowers
      (((E.E m.len σ).toD.comp
          (c.simplexPolynomialMap n.len m.len (SimplexCategory.Hom.toOrderHom f) σ).toRingHom).comp
        (algebraMap A (c.simplexPolynomial n.len (reindex f σ)))) := sorry

/-- The polynomial comparison sends the source kernel into the target envelope ideal. -/
theorem simplexPolynomialMap_toEnvelope_ideal
    {n m : SimplexCategory} (f : n ⟶ m) (σ : Fin (m.len + 1) → c.Λ) :
    Ideal.map
      ((E.E m.len σ).toD.comp
        (c.simplexPolynomialMap n.len m.len (SimplexCategory.Hom.toOrderHom f) σ).toRingHom)
      (c.simplexKernel n.len (reindex f σ)) ≤
      (E.E m.len σ).D.ideal := sorry

/-- Unique envelope lift `D_{σ ∘ f} ← P_{σ ∘ f}` through the target envelope. -/
noncomputable def envelopeLift {n m : SimplexCategory} (f : n ⟶ m)
    (σ : Fin (m.len + 1) → c.Λ) :
    (E.E n.len (reindex f σ)).D ⟶ (E.E m.len σ).D :=
  (E.hE n.len (reindex f σ)
      ((E.E m.len σ).toD.comp
        (c.simplexPolynomialMap n.len m.len (SimplexCategory.Hom.toOrderHom f) σ).toRingHom)
      (E.simplexPolynomialMap_toEnvelope_isDPMorphism f σ)
      (E.simplexPolynomialMap_toEnvelope_ideal f σ)).choose

/-- The envelope lift recovers the polynomial comparison on presentations. -/
theorem envelopeLift_spec {n m : SimplexCategory} (f : n ⟶ m)
    (σ : Fin (m.len + 1) → c.Λ) :
    (E.envelopeLift f σ).toRingHom.comp (E.E n.len (reindex f σ)).toD =
      (E.E m.len σ).toD.comp
        (c.simplexPolynomialMap n.len m.len (SimplexCategory.Hom.toOrderHom f) σ).toRingHom := sorry

/-- Powers of `(p)` pull back along the envelope lift. -/
theorem envelopeLift_span_pow {n m : SimplexCategory} (f : n ⟶ m)
    (σ : Fin (m.len + 1) → c.Λ) (k : ℕ) :
    Ideal.span {(p : (E.E n.len (reindex f σ)).D)} ^ k ≤
      (Ideal.span {(p : (E.E m.len σ).D)} ^ k).comap
        (E.envelopeLift f σ).toRingHom := sorry

/-- Stage maps of the completed envelope comparison. -/
noncomputable def homDStage {n m : SimplexCategory} (f : n ⟶ m)
    (σ : Fin (m.len + 1) → c.Λ) (k : ℕ) :
    AdicCompletion (Ideal.span {(p : (E.E n.len (reindex f σ)).D)})
      (E.E n.len (reindex f σ)).D →+*
      (E.E m.len σ).D ⧸ Ideal.span {(p : (E.E m.len σ).D)} ^ k :=
  (Ideal.quotientMap (Ideal.span {(p : (E.E m.len σ).D)} ^ k)
      (E.envelopeLift f σ).toRingHom (E.envelopeLift_span_pow f σ k)).comp
    (AdicCompletion.evalₐ (Ideal.span {(p : (E.E n.len (reindex f σ)).D)})
      k).toRingHom

/-- Compatibility of completed envelope stages with canonical factor maps. -/
theorem homDStage_compat {n m : SimplexCategory} (f : n ⟶ m)
    (σ : Fin (m.len + 1) → c.Λ) {a b : ℕ} (hle : a ≤ b) :
    (Ideal.Quotient.factorPow (Ideal.span {(p : (E.E m.len σ).D)}) hle).comp
        (E.homDStage f σ b) = E.homDStage f σ a := sorry

/-- Functorial completed PD-envelope maps `D_{σ ∘ f} → D_σ`. -/
noncomputable def homD {n m : SimplexCategory} (f : n ⟶ m)
    (σ : Fin (m.len + 1) → c.Λ) :
    envelopeCompletionRing p A (c.simplexPolynomial n.len (reindex f σ)) IA γA
      (c.simplexKernel n.len (reindex f σ)) (E.hIJ n.len (reindex f σ))
      (E.E n.len (reindex f σ)) (E.N n.len (reindex f σ))
      (E.hN n.len (reindex f σ)) (E.γhat n.len (reindex f σ)) →+*
      envelopeCompletionRing p A (c.simplexPolynomial m.len σ) IA γA (c.simplexKernel m.len σ)
        (E.hIJ m.len σ) (E.E m.len σ) (E.N m.len σ)
        (E.hN m.len σ) (E.γhat m.len σ) :=
  AdicCompletion.liftRingHom (Ideal.span {(p : (E.E m.len σ).D)})
    (fun k => E.homDStage f σ k)
    (fun {_ _} hle => E.homDStage_compat f σ hle)

/-- The completed comparison lifts the polynomial presentation map through both envelopes. -/
theorem homD_spec {n m : SimplexCategory} (f : n ⟶ m)
    (σ : Fin (m.len + 1) → c.Λ) :
    (E.homD f σ).comp
        ((envelopeCompletionMap p A
            (c.simplexPolynomial n.len (reindex f σ)) IA γA
            (c.simplexKernel n.len (reindex f σ))
            (E.hIJ n.len (reindex f σ)) (E.E n.len (reindex f σ))
            (E.N n.len (reindex f σ)) (E.hN n.len (reindex f σ))
            (E.γhat n.len (reindex f σ))).comp
          (E.E n.len (reindex f σ)).toD) =
      (envelopeCompletionMap p A (c.simplexPolynomial m.len σ) IA γA
          (c.simplexKernel m.len σ) (E.hIJ m.len σ) (E.E m.len σ)
          (E.N m.len σ) (E.hN m.len σ) (E.γhat m.len σ)).comp
        ((E.E m.len σ).toD.comp
          (c.simplexPolynomialMap n.len m.len (SimplexCategory.Hom.toOrderHom f) σ).toRingHom) := sorry

end CechCrisEnvelope

end EnvelopeMaps

end
