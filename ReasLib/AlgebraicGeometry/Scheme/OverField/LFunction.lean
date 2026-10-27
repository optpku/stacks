/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.SetLike.Fintype
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.RingTheory.FiniteType
public import Mathlib.AlgebraicGeometry.Cover.Open
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import ReasLib.CategoryTheory.Sites.LocallyConstant.Finite
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.ConstructibleTorFinite
public import ReasLib.LinearAlgebra.Determinant.EulerFactor
public import ReasLib.AlgebraicGeometry.Scheme.Etale.ClosedPointFrobenius

/-!
# L-functions of constructible étale sheaves over finite fields

This module defines the geometric Euler product
`L(X, F) = ∏_{x ∈ |X|} det(1 - π_x^* T^{deg x} | F_x̄)⁻¹` in `Λ⟦T⟧`,
realised coefficientwise by finite products over closed points of bounded
residue degree, together with its extension to `D_ctf(X, Λ)`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale
open AlgebraicGeometry.Scheme.Hom AlgebraicGeometry.SchemeOverField
open CategoryTheory.DerivedCategory CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k] [Fintype k]
variable {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k]
variable {Λ : Type u} [CommRing Λ] [Finite Λ] [IsNoetherianRing Λ]
variable [HasColimitsOfSize.{u, u} (ModuleCat.{u} Λ)]
variable [∀ {Y : Scheme.{u}}, HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ {Y : Scheme.{u}}, HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ {Y : Scheme.{u}} (U : Y.Etale),
    HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ {Y : Scheme.{u}}, Abelian (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [∀ {Y : Scheme.{u}},
    HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (F : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ),
    (smallEtalePullback f).op.HasLeftKanExtension F]
variable [∀ {Y : Scheme.{u}},
    (Y.smallEtaleTopology.W (A := ModuleCat.{u} Λ)).IsMonoidal]

/-!
The following private lemmas isolate the quotient step in the usual
finite-field argument.  They deliberately take the containment of the
Frobenius ideal as a hypothesis: this is the part which is supplied by the
finite residue-field calculation on an affine chart.  Thus the finite data
constructed here comes only from the actual quotient map and the finite set of
ideals of a finite ring.
-/

private theorem finite_bounded_maximalIdeals_of_quotient
    (A : Type*) [CommRing A] (I : Ideal A) [Finite (A ⧸ I)]
    (S : Set {m : Ideal A // m.IsMaximal})
    (hI : ∀ m : S, I ≤ (m.1 : Ideal A)) : S.Finite := by
  classical
  let f : S → Ideal (A ⧸ I) := fun m => (m.1 : Ideal A).map (Ideal.Quotient.mk I)
  have hf : Function.Injective f := by
    intro m m' h
    apply Subtype.ext
    apply Subtype.ext
    have hmap := congrArg (Ideal.comap (Ideal.Quotient.mk I)) h
    simpa only [f, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.mpr (hI m),
      sup_eq_left.mpr (hI m')] using hmap
  letI : Finite S := Finite.of_injective f hf
  exact Set.toFinite S

private theorem finite_bounded_maximalIdeals_of_integral_quotient
    (k A : Type*) [Field k] [CommRing A] [Algebra k A]
    [Algebra.FiniteType k A] [Finite k] (I : Ideal A)
    [Algebra.IsIntegral k (A ⧸ I)]
    (S : Set {m : Ideal A // m.IsMaximal})
    (hI : ∀ m : S, I ≤ (m.1 : Ideal A)) : S.Finite := by
  letI : Module.Finite k (A ⧸ I) := Algebra.IsIntegral.finite
  letI : Finite (A ⧸ I) := Module.finite_of_finite k
  exact finite_bounded_maximalIdeals_of_quotient A I S hI

private def frobeniusIdeal (k A : Type*) [CommRing A] [Fintype k] (n : ℕ) : Ideal A :=
  Ideal.span (Set.range (fun a : A => a ^ (Fintype.card k ^ n.factorial) - a))

private theorem algebra_isIntegral_quotient_frobenius
    (k A : Type*) [Field k] [CommRing A] [Algebra k A] [Fintype k] (n : ℕ) :
    Algebra.IsIntegral k (A ⧸ frobeniusIdeal k A n) := by
  rw [Algebra.isIntegral_def]
  intro x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  let N := Fintype.card k ^ n.factorial
  have hN : 1 < N := by
    dsimp [N]
    exact Nat.one_lt_pow (Nat.factorial_pos n).ne' Fintype.one_lt_card
  refine ⟨Polynomial.X ^ N - Polynomial.X, ?_, ?_⟩
  · apply Polynomial.monic_X_pow_sub
    rw [Polynomial.degree_X]
    exact_mod_cast hN
  · rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_X]
    change (Ideal.Quotient.mk (frobeniusIdeal k A n) a) ^ N -
      Ideal.Quotient.mk (frobeniusIdeal k A n) a = 0
    rw [← map_pow, ← _root_.map_sub]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨a, rfl⟩)

private theorem frobenius_mem_of_finrank_dvd
    (k K A : Type*) [Field k] [Field K] [CommRing A]
    [Algebra k K] [Fintype k] [Fintype K] [Algebra k A]
    (φ : A →ₐ[k] K) (a : A) (d n : ℕ)
    (hd : Module.finrank k K = d) (hdiv : d ∣ n.factorial) :
    φ (a ^ (Fintype.card k ^ n.factorial) - a) = 0 := by
  have hmul : d * (n.factorial / d) = n.factorial := Nat.mul_div_cancel' hdiv
  calc
    φ (a ^ (Fintype.card k ^ n.factorial) - a) =
        φ a ^ (Fintype.card k ^ n.factorial) - φ a := by simp
    _ = φ a ^ ((Fintype.card K) ^ (n.factorial / d)) - φ a := by
      rw [Module.card_eq_pow_finrank (K := k) (V := K), hd, ← pow_mul, hmul]
    _ = 0 := by simp only [FiniteField.pow_card_pow, sub_self]

private theorem frobeniusIdeal_le_maximal_of_finite_residue
    (k A : Type*) [Field k] [CommRing A] [Algebra k A] [Fintype k]
    (n : ℕ) (m : Ideal A) (hm : m.IsMaximal)
    (hfinite : Module.Finite k (A ⧸ m))
    (hpos : 0 < Module.finrank k (A ⧸ m))
    (hle : Module.finrank k (A ⧸ m) ≤ n) :
    frobeniusIdeal k A n ≤ m := by
  letI : Module.Finite k (A ⧸ m) := hfinite
  letI : Finite (A ⧸ m) := Module.finite_of_finite k
  letI : Fintype (A ⧸ m) := Fintype.ofFinite _
  letI : m.IsMaximal := hm
  letI : Field (A ⧸ m) := Ideal.Quotient.field m
  let φ : A →ₐ[k] (A ⧸ m) := Ideal.Quotient.mkₐ k m
  apply Ideal.span_le.2
  rintro _ ⟨a, rfl⟩
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  apply frobenius_mem_of_finrank_dvd k (A ⧸ m) A φ a
      (Module.finrank k (A ⧸ m)) n rfl
  exact Nat.dvd_factorial hpos hle

private theorem finite_bounded_maximalIdeals_of_frobenius
    (k A : Type*) [Field k] [CommRing A] [Algebra k A]
    [Algebra.FiniteType k A] [Fintype k] (n : ℕ)
    (S : Set {m : Ideal A // m.IsMaximal})
    (hfinite : ∀ m : S, Module.Finite k (A ⧸ (m.1 : Ideal A)))
    (hpos : ∀ m : S, 0 < Module.finrank k (A ⧸ (m.1 : Ideal A)))
    (hle : ∀ m : S, Module.finrank k (A ⧸ (m.1 : Ideal A)) ≤ n) :
    S.Finite := by
  letI : Algebra.IsIntegral k (A ⧸ frobeniusIdeal k A n) :=
    algebra_isIntegral_quotient_frobenius k A n
  apply finite_bounded_maximalIdeals_of_integral_quotient k A
    (frobeniusIdeal k A n) S
  intro m
  exact frobeniusIdeal_le_maximal_of_finite_residue k A n (m.1 : Ideal A)
    m.1.2 (hfinite m) (hpos m) (hle m)

/-- Zariski's lemma supplies finite, positive residue dimensions; in particular
the set in this lemma is empty when `n = 0`. -/
private theorem finite_maximalIdeals_finrankLE
    (k A : Type*) [Field k] [CommRing A] [Algebra k A]
    [Algebra.FiniteType k A] [Fintype k] (n : ℕ) :
    ({m : {m : Ideal A // m.IsMaximal} |
      Module.finrank k (A ⧸ (m : Ideal A)) ≤ n} : Set _).Finite := by
  apply finite_bounded_maximalIdeals_of_frobenius k A n
  · intro m
    letI : (m.1 : Ideal A).IsMaximal := m.1.2
    letI : Field (A ⧸ (m.1 : Ideal A)) := Ideal.Quotient.field _
    exact finite_of_finite_type_of_isJacobsonRing k (A ⧸ (m.1 : Ideal A))
  · intro m
    letI : (m.1 : Ideal A).IsMaximal := m.1.2
    letI : Field (A ⧸ (m.1 : Ideal A)) := Ideal.Quotient.field _
    letI : Module.Finite k (A ⧸ (m.1 : Ideal A)) :=
      finite_of_finite_type_of_isJacobsonRing k (A ⧸ (m.1 : Ideal A))
    exact Module.finrank_pos
  · exact fun m => m.2

/-- Exact degree transport along an affine open immersion.  Over a finite
field this can be proved from cardinalities of the canonical residue-field
isomorphisms, without choosing embeddings in a common extension. -/
private theorem residueDegree_eq_finrank_quotient
    [Fintype k] (X : SchemeOverField k) (A : CommRingCat.{u})
    [Algebra k A] [Algebra.FiniteType k A]
    (f : Spec A ⟶ X.left) [IsOpenImmersion f]
    (y : Spec A) (hy : y.asIdeal.IsMaximal) :
    X.hom.residueDegree (f y) = Module.finrank k (A ⧸ y.asIdeal) := by
  classical
  letI : y.asIdeal.IsMaximal := hy
  letI : Field (A ⧸ y.asIdeal) := Ideal.Quotient.field _
  letI : Module.Finite k (A ⧸ y.asIdeal) :=
    finite_of_finite_type_of_isJacobsonRing k (A ⧸ y.asIdeal)
  letI : Finite (A ⧸ y.asIdeal) := Module.finite_of_finite k
  let K₀ := (Spec (CommRingCat.of k)).residueField (X.hom (f y))
  let K₁ := X.left.residueField (f y)
  let e₀ : k ≃+* K₀ :=
    (Ideal.algEquivResidueFieldOfField (X.hom (f y)).asIdeal).toRingEquiv.trans
      (Spec.residueFieldIso (CommRingCat.of k) (X.hom (f y))).commRingCatIsoToRingEquiv.symm
  let e₁ : (A ⧸ y.asIdeal) ≃+* K₁ :=
    ((RingEquiv.ofBijective (algebraMap (A ⧸ y.asIdeal) y.asIdeal.ResidueField)
      (Ideal.bijective_algebraMap_quotient_residueField y.asIdeal)).trans
        (Spec.residueFieldIso A y).commRingCatIsoToRingEquiv.symm).trans
          (asIso (f.residueFieldMap y)).commRingCatIsoToRingEquiv.symm
  letI : Finite K₀ := Finite.of_equiv k e₀.toEquiv
  letI : Finite K₁ := Finite.of_equiv (A ⧸ y.asIdeal) e₁.toEquiv
  letI : Fintype K₀ := Fintype.ofFinite _
  letI : Fintype K₁ := Fintype.ofFinite _
  letI : Fintype (A ⧸ y.asIdeal) := Fintype.ofFinite _
  letI : Algebra K₀ K₁ := (X.hom.residueFieldMap (f y)).hom.toAlgebra
  change Module.finrank K₀ K₁ = Module.finrank k (A ⧸ y.asIdeal)
  apply Nat.pow_right_injective (Nat.succ_le_of_lt (Fintype.one_lt_card (α := k)))
  calc
    Fintype.card k ^ Module.finrank K₀ K₁ =
        Fintype.card K₀ ^ Module.finrank K₀ K₁ := by
      rw [Fintype.card_congr e₀.toEquiv]
    _ = Fintype.card K₁ := (Module.card_eq_pow_finrank (K := K₀) (V := K₁)).symm
    _ = Fintype.card (A ⧸ y.asIdeal) := (Fintype.card_congr e₁.toEquiv).symm
    _ = Fintype.card k ^ Module.finrank k (A ⧸ y.asIdeal) :=
      Module.card_eq_pow_finrank (K := k) (V := A ⧸ y.asIdeal)

/-- Bounded closed points lying in a single affine chart form a finite set.
The injection remembers the actual prime ideal, rather than a choice of a
residue-field embedding. -/
private theorem finite_closedPoints_in_affine_chart
    [Fintype k] (X : SchemeOverField k) [LocallyOfFiniteType X.hom]
    (A : CommRingCat.{u}) (f : Spec A ⟶ X.left) [IsOpenImmersion f] (n : ℕ) :
    Finite {y : Spec A // IsClosed {f y} ∧ X.hom.residueDegree (f y) ≤ n} := by
  classical
  let φ := Spec.preimage (f ≫ X.hom)
  letI : Algebra k A := φ.hom.toAlgebra
  letI : Algebra.FiniteType k A := by
    change φ.hom.FiniteType
    apply (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType) (φ := φ)).mp
    change LocallyOfFiniteType (Spec.map (Spec.preimage (f ≫ X.hom)))
    rw [Spec.map_preimage]
    infer_instance
  let S : Set {m : Ideal A // m.IsMaximal} :=
    {m | Module.finrank k (A ⧸ (m : Ideal A)) ≤ n}
  have hS : S.Finite := finite_maximalIdeals_finrankLE k A n
  letI : Finite S := hS
  have hm (y : {y : Spec A // IsClosed {f y} ∧ X.hom.residueDegree (f y) ≤ n}) :
      y.1.asIdeal.IsMaximal := by
    apply (PrimeSpectrum.isClosed_singleton_iff_isMaximal y.1).mp
    exact preimage_closedPoints_subset f.isOpenEmbedding.injective f.continuous y.2.1
  let g : {y : Spec A // IsClosed {f y} ∧ X.hom.residueDegree (f y) ≤ n} → S :=
    fun y => ⟨⟨y.1.asIdeal, hm y⟩, by
      change Module.finrank k (A ⧸ y.1.asIdeal) ≤ n
      rw [← residueDegree_eq_finrank_quotient X A f y.1 (hm y)]
      exact y.2.2⟩
  apply Finite.of_injective g
  intro y z h
  apply Subtype.ext
  apply PrimeSpectrum.ext
  exact congrArg (fun m : S => (m.1 : Ideal A)) h

/-- There are only finitely many closed points of residue degree at most `n`
on a finite-type scheme over a finite field. -/
instance finite_closedPoints_residueDegreeLE [Fintype k] (X : SchemeOverField k)
    [Scheme.Hom.FiniteType X.hom] (n : ℕ) :
    Finite {x : closedPoints X.left // X.hom.residueDegree x.1 ≤ n} := by
  classical
  letI : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  let 𝒰 := X.left.affineCover.finiteSubcover
  let A (i : 𝒰.I₀) := Γ(𝒰.X i, ⊤)
  let f (i : 𝒰.I₀) : Spec (A i) ⟶ X.left := (𝒰.X i).isoSpec.inv ≫ 𝒰.f i
  let T (i : 𝒰.I₀) :=
    {y : Spec (A i) // IsClosed {f i y} ∧ X.hom.residueDegree (f i y) ≤ n}
  letI (i : 𝒰.I₀) : IsOpenImmersion (f i) := by dsimp [f]; infer_instance
  letI (i : 𝒰.I₀) : Finite (T i) := finite_closedPoints_in_affine_chart X (A i) (f i) n
  let g : (Σ i : 𝒰.I₀, T i) →
      {x : closedPoints X.left // X.hom.residueDegree x.1 ≤ n} :=
    fun ⟨i, y⟩ => ⟨⟨f i y.1, y.2.1⟩, y.2.2⟩
  apply Finite.of_surjective g
  intro x
  obtain ⟨i, z, hz⟩ := 𝒰.exists_eq x.1.1
  let y : Spec (A i) := (𝒰.X i).isoSpec.hom z
  have hy : f i y = x.1.1 := by simpa [f, y, ← Scheme.Hom.comp_apply] using hz
  refine ⟨⟨i, y, ?_⟩, ?_⟩
  · exact ⟨hy.symm ▸ x.1.2, hy.symm ▸ x.2⟩
  · apply Subtype.ext
    apply Subtype.ext
    exact hy

/-- A `Fintype` structure on the finite set of closed points of residue degree
at most `n`. -/
instance fintype_closedPoints_residueDegreeLE [Fintype k] (X : SchemeOverField k)
    [Scheme.Hom.FiniteType X.hom] (n : ℕ) :
    Fintype {x : closedPoints X.left // X.hom.residueDegree x.1 ≤ n} :=
  Fintype.ofFinite _

/-- The field-extension degree `[κ(x) : k]` is the residue degree of the structure
morphism at `x`. -/
theorem deg_eq_residueDegree (X : SchemeOverField k) (x : X.left) :
    X.hom.residueDegree x = Module.finrank k (X.left.residueField x) := sorry

/-- The local Euler factor of a constructible flat étale sheaf at a closed
point. -/
def eulerFactorClosedStalk (X : SchemeOverField k)
    [Scheme.Hom.FiniteType X.hom]
    (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (hcons : Sheaf.IsConstructibleEtaleModule
      (fun {Y} f ↦ (Sheaf.smallEtaleInverseImage f (ModuleCat.{u} Λ)).obj)
      (fun {Y} G ↦ Sheaf.IsFiniteTypeLocallyConstantModule G) F)
    [IsFlat F] (x : closedPoints X.left) : PowerSeries Λ :=
  -- Local instance justification (proof-local temporary data): finite generation of a constructible-flat stalk is a consequence of the explicit constructible hypothesis, which is not a typeclass.
  haveI : Module.Finite Λ (geometricStalkClosed F x) :=
    finite_geometricStalkClosed F hcons x
  -- Local instance justification (proof-local temporary data): projectivity of a constructible-flat stalk is a consequence of `IsFlat` together with the explicit constructible hypothesis, which cannot register a global instance.
  haveI : Module.Projective Λ (geometricStalkClosed F x) :=
    projective_geometricStalkClosed F hcons x
  LinearMap.eulerFactor (geometricFrobeniusClosedStalk F x) (X.hom.residueDegree x.1)

/-- The constant coefficient of a closed-point Euler factor is `1`. -/
theorem constantCoeff_eulerFactorClosedStalk (X : SchemeOverField k)
    [Scheme.Hom.FiniteType X.hom]
    (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (hcons : Sheaf.IsConstructibleEtaleModule
      (fun {Y} f ↦ (Sheaf.smallEtaleInverseImage f (ModuleCat.{u} Λ)).obj)
      (fun {Y} G ↦ Sheaf.IsFiniteTypeLocallyConstantModule G) F)
    [IsFlat F] (x : closedPoints X.left) :
    PowerSeries.constantCoeff (eulerFactorClosedStalk X F hcons x) = 1 := sorry

/-- The L-function of a constructible flat étale sheaf of `Λ`-modules on a
finite-type scheme over a finite field, as the Euler product over closed
points of the local factors `det(1 - π_x^* T^{deg x} | F_x̄)⁻¹`. -/
def lFunction [Fintype k] (X : SchemeOverField k) [Scheme.Hom.FiniteType X.hom]
    (hΛ : Nat.Coprime (Nat.card Λ) p)
    (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (hcons : Sheaf.IsConstructibleEtaleModule
      (fun {Y} f ↦ (Sheaf.smallEtaleInverseImage f (ModuleCat.{u} Λ)).obj)
      (fun {Y} G ↦ Sheaf.IsFiniteTypeLocallyConstantModule G) F)
    [IsFlat F] : PowerSeries Λ :=
  PowerSeries.mk fun n =>
    PowerSeries.coeff n
      (∏ x : {x : closedPoints X.left // X.hom.residueDegree x.1 ≤ n},
        eulerFactorClosedStalk X F hcons x.1)

/-- The coefficient of `T^n` in `lFunction` is the corresponding coefficient of
the finite product of Euler factors over closed points of residue degree at
most `n`. -/
theorem lFunction_coeff (X : SchemeOverField k) [Scheme.Hom.FiniteType X.hom]
    (hΛ : Nat.Coprime (Nat.card Λ) p)
    (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (hcons : Sheaf.IsConstructibleEtaleModule
      (fun {Y} f ↦ (Sheaf.smallEtaleInverseImage f (ModuleCat.{u} Λ)).obj)
      (fun {Y} G ↦ Sheaf.IsFiniteTypeLocallyConstantModule G) F)
    [IsFlat F] (n : ℕ) :
    PowerSeries.coeff n (lFunction X hΛ F hcons) =
      PowerSeries.coeff n
        (∏ x : {x : closedPoints X.left // X.hom.residueDegree x.1 ≤ n},
          eulerFactorClosedStalk X F hcons x.1) := sorry

/-- The L-function is the Euler product over closed points of the local
factors `det(1 - π_x^* T^{deg x} | F_x̄)⁻¹`, realised coefficientwise by
finite products over residue degree at most `n`. -/
theorem lFunction_spec (X : SchemeOverField k) [Scheme.Hom.FiniteType X.hom]
    (hΛ : Nat.Coprime (Nat.card Λ) p)
    (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (hcons : Sheaf.IsConstructibleEtaleModule
      (fun {Y} f ↦ (Sheaf.smallEtaleInverseImage f (ModuleCat.{u} Λ)).obj)
      (fun {Y} G ↦ Sheaf.IsFiniteTypeLocallyConstantModule G) F)
    [IsFlat F] :
    lFunction X hΛ F hcons =
      PowerSeries.mk fun n =>
        PowerSeries.coeff n
          (∏ x : {x : closedPoints X.left // X.hom.residueDegree x.1 ≤ n},
            eulerFactorClosedStalk X F hcons x.1) := sorry

variable [∀ {Y : Scheme.{u}} (U : Y.Etale),
    Abelian (Sheaf (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ))]
variable [∀ {Y : Scheme.{u}} (U : Y.Etale),
    HasDerivedCategory (Sheaf (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ))]
variable [∀ {Y : Scheme.{u}} (U : Y.Etale),
    ((Y.smallEtaleTopology.over U).W (A := ModuleCat.{u} Λ)).IsMonoidal]

/-- The local Euler factor of an object of `D_ctf(X, Λ)` at a closed point,
using an explicit perfectness hypothesis on the geometric stalk. This
hypothesis records the stalkwise perfectness required for the derived determinant. -/
def eulerFactorDerivedStalk (X : SchemeOverField k)
    [Scheme.Hom.FiniteType X.hom]
    (K : Scheme.Etale.Derived.ConstructibleTorFinite X.left Λ)
    (x : closedPoints X.left)
    (hperf : DerivedCategory.IsPerfect (geometricDerivedStalkClosed K.obj x)) :
    PowerSeries Λ :=
  hperf.eulerFactor
    (geometricFrobeniusDerivedStalkClosed K.obj x) (X.hom.residueDegree x.1)

/-- Unfolding of the derived closed-point Euler factor. -/
theorem eulerFactorDerivedStalk_def (X : SchemeOverField k)
    [Scheme.Hom.FiniteType X.hom]
    (K : Scheme.Etale.Derived.ConstructibleTorFinite X.left Λ)
    (x : closedPoints X.left)
    (hperf : DerivedCategory.IsPerfect (geometricDerivedStalkClosed K.obj x)) :
    eulerFactorDerivedStalk X K x hperf =
      hperf.eulerFactor
        (geometricFrobeniusDerivedStalkClosed K.obj x)
        (X.hom.residueDegree x.1) := sorry

/-- The L-function of an object of `D_ctf(X, Λ)`, as the Euler product over
closed points of the local factors `det(1 - π_x^* T^{deg x} | K_x̄)⁻¹`.
The extra `hperf` hypothesis records that geometric stalks are perfect,
which is the stalkwise content of finite Tor dimension. -/
def lFunctionDerived [Fintype k] (X : SchemeOverField k) [Scheme.Hom.FiniteType X.hom]
    (hΛ : Nat.Coprime (Nat.card Λ) p)
    (K : Scheme.Etale.Derived.ConstructibleTorFinite X.left Λ)
    (hperf : ∀ x : closedPoints X.left,
      DerivedCategory.IsPerfect (geometricDerivedStalkClosed K.obj x)) :
    PowerSeries Λ :=
  PowerSeries.mk fun n ↦
    PowerSeries.coeff n
      (∏ x : {x : closedPoints X.left // X.hom.residueDegree x.1 ≤ n},
        eulerFactorDerivedStalk X K x.1 (hperf x.1))

/-- The coefficient of `T^n` in `lFunctionDerived` is the corresponding
coefficient of the finite product of derived Euler factors over closed points
of residue degree at most `n`. -/
theorem lFunctionDerived_coeff (X : SchemeOverField k)
    [Scheme.Hom.FiniteType X.hom] (hΛ : Nat.Coprime (Nat.card Λ) p)
    (K : Scheme.Etale.Derived.ConstructibleTorFinite X.left Λ)
    (hperf : ∀ x : closedPoints X.left,
      DerivedCategory.IsPerfect (geometricDerivedStalkClosed K.obj x))
    (n : ℕ) :
    PowerSeries.coeff n (lFunctionDerived X hΛ K hperf) =
      PowerSeries.coeff n
        (∏ x : {x : closedPoints X.left // X.hom.residueDegree x.1 ≤ n},
          eulerFactorDerivedStalk X K x.1 (hperf x.1)) := sorry

/-- On a constructible flat sheaf placed in degree zero, the sheaf-theoretic
L-function agrees with the derived L-function. -/
theorem lFunctionDerived_single (X : SchemeOverField k)
    [Scheme.Hom.FiniteType X.hom] (hΛ : Nat.Coprime (Nat.card Λ) p)
    (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (hcons : Sheaf.IsConstructibleEtaleModule
      (fun {Y} f ↦ (Sheaf.smallEtaleInverseImage f (ModuleCat.{u} Λ)).obj)
      (fun {Y} G ↦ Sheaf.IsFiniteTypeLocallyConstantModule G) F)
    [IsFlat F]
    (K : Scheme.Etale.Derived.ConstructibleTorFinite X.left Λ)
    (hperf : ∀ x : closedPoints X.left,
      DerivedCategory.IsPerfect (geometricDerivedStalkClosed K.obj x))
    (hK : K.obj =
      (DerivedCategory.singleFunctor
        (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) (0 : ℤ)).obj F) :
    lFunction X hΛ F hcons = lFunctionDerived X hΛ K hperf := sorry

end AlgebraicGeometry.SchemeOverField
