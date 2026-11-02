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
        (E.hIJ n σ) (E.E n σ) := by
  exact ⟨E.hIJ n σ, E.hN n σ, E.hE n σ⟩

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

private theorem restriction_comp {U V W : X.Opens} (hUV : V ≤ U) (hVW : W ≤ V) :
    (restriction hVW).comp (restriction hUV) = restriction (hVW.trans hUV) := by
  exact congrArg CommRingCat.Hom.hom
    (X.presheaf.map_comp (homOfLE hUV).op (homOfLE hVW).op).symm

private theorem simplexSurjection_tmul (c : CechCrisCover x₀)
    (n : ℕ) (σ : Fin (n + 2) → c.Λ)
    (a : c.polynomial (σ 0)) (b : c.simplexPolynomial n (fun i => σ i.succ)) :
    c.simplexSurjection (n + 1) σ (a ⊗ₜ[A] b) =
      restriction (c.simplexOpen_le_member (n + 1) σ 0) (c.π (σ 0) a) *
        restriction (c.simplexOpen_succ_le n σ)
          (c.simplexSurjection n (fun i => σ i.succ) b) := rfl

private theorem simplexPolynomialMap_tmul (c : CechCrisCover x₀) (n m : ℕ)
    (f : Fin (n + 2) → Fin (m + 1)) (σ : Fin (m + 1) → c.Λ)
    (a : c.polynomial (σ (f 0)))
    (b : c.simplexPolynomial n (fun i => σ (f i.succ))) :
    c.simplexPolynomialMap (n + 1) m f σ (a ⊗ₜ[A] b) =
      c.simplexPolynomialSlot m σ (f 0) a *
        c.simplexPolynomialMap n m (fun i => f i.succ) σ b := rfl

private theorem simplexSurjection_slot (c : CechCrisCover x₀) (m : ℕ) (σ : Fin (m + 1) → c.Λ)
    (i : Fin (m + 1)) (a : c.polynomial (σ i)) :
    c.simplexSurjection m σ (c.simplexPolynomialSlot m σ i a) =
      restriction (c.simplexOpen_le_member m σ i) (c.π (σ i) a) := by
  induction m with
  | zero =>
    have hi : i = 0 := Fin.eq_zero i
    subst i
    rfl
  | succ m ih =>
    revert a
    refine Fin.cases ?_ (fun j => ?_) i
    · intro a
      change c.simplexSurjection (m + 1) σ
        (a ⊗ₜ[A] (1 : c.simplexPolynomial m (fun i => σ i.succ))) = _
      rw [simplexSurjection_tmul c]
      have htail1 := (c.simplexSurjection m (fun i => σ i.succ)).map_one
      have h1 := (restriction (c.simplexOpen_succ_le m σ)).map_one
      have htail1' : restriction (c.simplexOpen_succ_le m σ)
          (c.simplexSurjection m (fun i => σ i.succ) 1) = 1 := by
        calc
          _ = restriction (c.simplexOpen_succ_le m σ) 1 := congrArg _ htail1
          _ = 1 := h1
      rw [htail1', mul_one]
    · intro a
      change c.simplexSurjection (m + 1) σ
        ((1 : c.polynomial (σ 0)) ⊗ₜ[A]
          (c.simplexPolynomialSlot m (fun i => σ i.succ) j a)) = _
      rw [simplexSurjection_tmul c]
      simp only [map_one, one_mul]
      rw [ih]
      exact congrArg (fun h => h (c.π (σ j.succ) a))
        (restriction_comp (c.simplexOpen_le_member m (fun i => σ i.succ) j)
          (c.simplexOpen_succ_le m σ))

private theorem simplexSurjection_map (c : CechCrisCover x₀) (n m : ℕ) (f : Fin (n + 1) → Fin (m + 1))
    (σ : Fin (m + 1) → c.Λ) :
    (c.simplexSurjection m σ).toRingHom.comp
        (c.simplexPolynomialMap n m f σ).toRingHom =
      (restriction (c.simplexOpen_reindex_le f σ)).comp
        (c.simplexSurjection n (fun i => σ (f i))).toRingHom := by
  induction n with
  | zero =>
    apply RingHom.ext
    intro a
    change c.simplexSurjection m σ (c.simplexPolynomialSlot m σ (f 0) a) =
      restriction (c.simplexOpen_reindex_le f σ)
        (restriction (le_of_eq (c.simplexOpen_zero (fun i => σ (f i))))
          (c.π (σ (f 0)) a))
    rw [simplexSurjection_slot c]
    exact (congrArg (fun h => h (c.π (σ (f 0)) a))
      (restriction_comp (le_of_eq (c.simplexOpen_zero (fun i => σ (f i))))
        (c.simplexOpen_reindex_le f σ))).symm
  | succ n ih =>
    apply Algebra.TensorProduct.ringHom_ext (R := A)
    · apply RingHom.ext
      intro a
      change c.simplexSurjection m σ
          (c.simplexPolynomialMap (n + 1) m f σ
            (a ⊗ₜ[A] (1 : c.simplexPolynomial n (fun i => σ (f i.succ))))) =
        restriction (c.simplexOpen_reindex_le f σ)
          (c.simplexSurjection (n + 1) (fun i => σ (f i))
            (a ⊗ₜ[A] (1 : c.simplexPolynomial n (fun i => σ (f i.succ)))))
      rw [simplexPolynomialMap_tmul c, simplexSurjection_tmul c]
      have hpoly1 := (c.simplexPolynomialMap n m (fun i => f i.succ) σ).map_one
      have htail1 := (c.simplexSurjection n (fun i => σ (f i.succ))).map_one
      have h1 := (restriction (c.simplexOpen_succ_le n (fun i => σ (f i)))).map_one
      have hpoly1' : c.simplexPolynomialMap n m (fun i => f i.succ) σ 1 = 1 := hpoly1
      have htail1' : restriction (c.simplexOpen_succ_le n (fun i => σ (f i)))
          (c.simplexSurjection n (fun i => σ (f i.succ)) 1) = 1 := by
        calc
          _ = restriction (c.simplexOpen_succ_le n (fun i => σ (f i))) 1 := congrArg _ htail1
          _ = 1 := h1
      rw [hpoly1', htail1', mul_one]
      rw [simplexSurjection_slot c]
      simp only [mul_one]
      exact (congrArg (fun h => h (c.π (σ (f 0)) a))
        (restriction_comp (c.simplexOpen_le_member (n + 1) (fun i => σ (f i)) 0)
          (c.simplexOpen_reindex_le f σ))).symm
    · apply RingHom.ext
      intro a
      change c.simplexSurjection m σ
          (c.simplexPolynomialMap (n + 1) m f σ
            ((1 : c.polynomial (σ (f 0))) ⊗ₜ[A] a)) =
        restriction (c.simplexOpen_reindex_le f σ)
          (c.simplexSurjection (n + 1) (fun i => σ (f i))
            ((1 : c.polynomial (σ (f 0))) ⊗ₜ[A] a))
      rw [simplexPolynomialMap_tmul c, simplexSurjection_tmul c]
      have hslot1 := (c.simplexPolynomialSlot m σ (f 0)).map_one
      have hπ1 := (c.π (σ (f 0))).map_one
      have hslot1' : c.simplexPolynomialSlot m σ (f 0) 1 = 1 := hslot1
      have hπ1' : restriction (c.simplexOpen_le_member (n + 1) (fun i => σ (f i)) 0)
          (c.π (σ (f 0)) 1) = 1 := by
        calc
          _ = restriction (c.simplexOpen_le_member (n + 1) (fun i => σ (f i)) 0) 1 := congrArg _ hπ1
          _ = 1 := (restriction (c.simplexOpen_le_member (n + 1) (fun i => σ (f i)) 0)).map_one
      rw [hslot1', hπ1', one_mul]
      have h := congrArg (fun h => h a) (ih (fun i => f i.succ))
      change c.simplexSurjection m σ
          (c.simplexPolynomialMap n m (fun i => f i.succ) σ a) =
        restriction (c.simplexOpen_reindex_le (fun i => f i.succ) σ)
          (c.simplexSurjection n (fun i => σ (f i.succ)) a) at h
      rw [h]
      simp only [one_mul]
      exact (congrArg (fun h => h (c.simplexSurjection n (fun i => σ (f i.succ)) a))
        (restriction_comp (c.simplexOpen_succ_le n (fun i => σ (f i)))
          (c.simplexOpen_reindex_le f σ))).symm

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
        (algebraMap A (c.simplexPolynomial n.len (reindex f σ)))) := by
  have hmap :
      (c.simplexPolynomialMap n.len m.len
          (SimplexCategory.Hom.toOrderHom f) σ).toRingHom.comp
          (algebraMap A (c.simplexPolynomial n.len (reindex f σ))) =
        algebraMap A (c.simplexPolynomial m.len σ) := by
    ext a
    exact (c.simplexPolynomialMap n.len m.len
      (SimplexCategory.Hom.toOrderHom f) σ).commutes a
  rw [RingHom.comp_assoc, hmap, ← (E.E m.len σ).base_toD]
  exact (E.E m.len σ).base.isDPMorphism

/-- The polynomial comparison sends the source kernel into the target envelope ideal. -/
theorem simplexPolynomialMap_toEnvelope_ideal
    {n m : SimplexCategory} (f : n ⟶ m) (σ : Fin (m.len + 1) → c.Λ) :
    Ideal.map
      ((E.E m.len σ).toD.comp
        (c.simplexPolynomialMap n.len m.len (SimplexCategory.Hom.toOrderHom f) σ).toRingHom)
      (c.simplexKernel n.len (reindex f σ)) ≤
      (E.E m.len σ).D.ideal := by
  apply Ideal.map_le_iff_le_comap.mpr
  intro a ha
  have ha0 : c.simplexSurjection n.len (reindex f σ) a = 0 := ha
  have hmap :
      c.simplexPolynomialMap n.len m.len (SimplexCategory.Hom.toOrderHom f) σ a ∈
        c.simplexKernel m.len σ := by
    change c.simplexSurjection m.len σ
      (c.simplexPolynomialMap n.len m.len (SimplexCategory.Hom.toOrderHom f) σ a) = 0
    have h := congrArg (fun h => h a)
      (simplexSurjection_map c n.len m.len (SimplexCategory.Hom.toOrderHom f) σ)
    change c.simplexSurjection m.len σ
        (c.simplexPolynomialMap n.len m.len (SimplexCategory.Hom.toOrderHom f) σ a) =
      restriction (c.simplexOpen_reindex_le (SimplexCategory.Hom.toOrderHom f) σ)
        (c.simplexSurjection n.len (reindex f σ) a) at h
    exact h.trans ((congrArg _ ha0).trans (map_zero _))
  exact (E.E m.len σ).ideal_map (Ideal.mem_map_of_mem (E.E m.len σ).toD hmap)

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
        (c.simplexPolynomialMap n.len m.len (SimplexCategory.Hom.toOrderHom f) σ).toRingHom := by
  exact (E.hE n.len (reindex f σ)
      ((E.E m.len σ).toD.comp
        (c.simplexPolynomialMap n.len m.len (SimplexCategory.Hom.toOrderHom f) σ).toRingHom)
      (E.simplexPolynomialMap_toEnvelope_isDPMorphism f σ)
      (E.simplexPolynomialMap_toEnvelope_ideal f σ)).choose_spec.1

/-- Powers of `(p)` pull back along the envelope lift. -/
theorem envelopeLift_span_pow {n m : SimplexCategory} (f : n ⟶ m)
    (σ : Fin (m.len + 1) → c.Λ) (k : ℕ) :
    Ideal.span {(p : (E.E n.len (reindex f σ)).D)} ^ k ≤
      (Ideal.span {(p : (E.E m.len σ).D)} ^ k).comap
        (E.envelopeLift f σ).toRingHom := by
  apply Ideal.map_le_iff_le_comap.mp
  rw [Ideal.map_pow, Ideal.map_span, Set.image_singleton]
  simpa using (le_rfl :
    Ideal.span {(p : (E.E m.len σ).D)} ^ k ≤
      Ideal.span {(p : (E.E m.len σ).D)} ^ k)

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
        (E.homDStage f σ b) = E.homDStage f σ a := by
  apply RingHom.ext
  intro x
  let R := (E.E n.len (reindex f σ)).D
  let I := Ideal.span {(p : R)}
  have hEval :
      Ideal.Quotient.factorPow I hle (AdicCompletion.evalₐ I b x) =
        AdicCompletion.evalₐ I a x := by
    obtain ⟨sequence, rfl⟩ := AdicCompletion.mk_surjective I R x
    simp only [AdicCompletion.evalₐ_mk, Ideal.Quotient.factor_mk]
    exact congrArg (Ideal.Quotient.factor
      (show (I ^ a • ⊤ : Ideal R) ≤ I ^ a by
        rw [Ideal.smul_eq_mul, Ideal.mul_top]))
      (AdicCompletion.AdicCauchySequence.mk_eq_mk hle sequence)
  change Ideal.Quotient.factorPow (Ideal.span {(p : (E.E m.len σ).D)}) hle
      (Ideal.quotientMap _ (E.envelopeLift f σ).toRingHom
        (E.envelopeLift_span_pow f σ b) (AdicCompletion.evalₐ I b x)) =
    Ideal.quotientMap _ (E.envelopeLift f σ).toRingHom
      (E.envelopeLift_span_pow f σ a) (AdicCompletion.evalₐ I a x)
  rw [← hEval]
  generalize AdicCompletion.evalₐ I b x = z
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
  rfl

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
          (c.simplexPolynomialMap n.len m.len (SimplexCategory.Hom.toOrderHom f) σ).toRingHom) := by
  apply RingHom.ext
  intro x
  apply AdicCompletion.ext_evalₐ
  intro k
  change AdicCompletion.evalₐ (Ideal.span {(p : (E.E m.len σ).D)}) k
      ((AdicCompletion.liftRingHom (Ideal.span {(p : (E.E m.len σ).D)})
          (fun j => E.homDStage f σ j) (fun {_ _} h => E.homDStage_compat f σ h))
        (AdicCompletion.of (Ideal.span {(p : (E.E n.len (reindex f σ)).D)})
          (E.E n.len (reindex f σ)).D ((E.E n.len (reindex f σ)).toD x))) =
    AdicCompletion.evalₐ (Ideal.span {(p : (E.E m.len σ).D)}) k
      (AdicCompletion.of (Ideal.span {(p : (E.E m.len σ).D)}) (E.E m.len σ).D
        ((E.E m.len σ).toD
          (c.simplexPolynomialMap n.len m.len (SimplexCategory.Hom.toOrderHom f) σ x)))
  rw [AdicCompletion.evalₐ_liftRingHom]
  simp only [homDStage, RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
    AdicCompletion.evalₐ_of, Ideal.quotientMap_mk]
  exact congrArg (Ideal.Quotient.mk (Ideal.span {(p : (E.E m.len σ).D)} ^ k))
    (congrArg (fun h => h x) (E.envelopeLift_spec f σ))

end CechCrisEnvelope

end EnvelopeMaps

end
