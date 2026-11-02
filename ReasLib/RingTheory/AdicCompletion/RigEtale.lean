/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.RingTheory.Noetherian.Basic
public import ReasLib.RingTheory.Topology.Adic.Complete
public import ReasLib.RingTheory.Topology.Adic.Hom
public import ReasLib.RingTheory.AdicCompletion.TopologicallyFiniteType
public import ReasLib.RingTheory.AdicCompletion.NaiveCotangent

/-!
# Rig-étale algebras and continuous homomorphisms

An algebra over a Noetherian pair `(A, I)` is rig-étale when it is
topologically of finite type and some power of `I` annihilates the homology of
the completed naive cotangent complex `NL_{B/A}^∧` in degrees `1` and `0`. A
continuous homomorphism of adic Noetherian topological rings is rig-étale when
this holds for some, equivalently any, ideal of definition of `A` that also
induces the ambient topology on `B`.
-/

@[expose] public section

universe u

namespace Algebra

variable {A : Type u} [CommRing A]

/-- Every `a ∈ I ^ c` annihilates homology of a finite completed naive
cotangent complex of `B` over `(A, I)` in degrees `1` and `0`. -/
def annihilatesNaiveCotangent (I : Ideal A) (B : Type u) [CommRing B] [Algebra A B]
    (c : ℕ) : Prop :=
  ∃ (ι : Type u) (_ : Fintype ι) (P : NaiveCotangent.Adic.Presentation A B I ι),
    ∀ a ∈ I ^ c,
      (∀ x : ((NaiveCotangent.Adic.naiveCotangent I P).homology 1 : Type u),
          (algebraMap A B a) • x = 0) ∧
        ∀ x : ((NaiveCotangent.Adic.naiveCotangent I P).homology 0 : Type u),
          (algebraMap A B a) • x = 0

/-- Annihilation of completed naive cotangent homology unpacks as the existence
of a finite presentation whose homology in degrees `1` and `0` is killed by
every element of `I ^ c`. -/
theorem annihilatesNaiveCotangent_iff (I : Ideal A) (B : Type u) [CommRing B]
    [Algebra A B] (c : ℕ) :
    annihilatesNaiveCotangent I B c ↔
      ∃ (ι : Type u) (_ : Fintype ι) (P : NaiveCotangent.Adic.Presentation A B I ι),
        ∀ a ∈ I ^ c,
          (∀ x : ((NaiveCotangent.Adic.naiveCotangent I P).homology 1 : Type u),
              (algebraMap A B a) • x = 0) ∧
            ∀ x : ((NaiveCotangent.Adic.naiveCotangent I P).homology 0 : Type u),
              (algebraMap A B a) • x = 0 :=
  Iff.rfl

/-- An `A`-algebra `B` is rig-étale over the pair `(A, I)` when it is
topologically of finite type and some power of `I` annihilates completed naive
cotangent homology. -/
class RigEtale (I : Ideal A) (B : Type u) [CommRing B] [Algebra A B] : Prop
    extends TopologicallyFiniteType I B where
  /-- Some power of `I` annihilates completed naive cotangent homology. -/
  exists_pow_annihilates : ∃ c : ℕ, annihilatesNaiveCotangent I B c

namespace RigEtale

/-- The identity algebra is rig-étale over `(A, I)` whenever `A` is `I`-adically
complete. -/
instance id (I : Ideal A) [IsAdicComplete I A] : RigEtale I A := by
  classical
  let e₀ := (MvPolynomial.isEmptyAlgEquiv A PEmpty).symm
  have hpoly : IsAdicComplete (NaiveCotangent.Adic.polynomialIdeal A I PEmpty)
      (MvPolynomial PEmpty A) := by
    have h := (IsAdicComplete.congr_ringEquiv I e₀.toRingEquiv).mpr inferInstance
    change IsAdicComplete (I.map e₀.toRingHom) (MvPolynomial PEmpty A) at h
    simpa only [NaiveCotangent.Adic.polynomialIdeal_eq_map, e₀,
      MvPolynomial.isEmptyAlgEquiv_symm_toRingHom, MvPolynomial.algebraMap_eq] using h
  letI := hpoly
  let e : NaiveCotangent.Adic.polynomialCompletion A I PEmpty ≃ₐ[A] A :=
    ((AdicCompletion.ofAlgEquiv
      (NaiveCotangent.Adic.polynomialIdeal A I PEmpty)).restrictScalars A).symm.trans
        (MvPolynomial.isEmptyAlgEquiv A PEmpty)
  let P : NaiveCotangent.Adic.Presentation A A I PEmpty := ⟨e.toAlgHom, e.surjective⟩
  have hker (g : P.toExtension.ker) : g = 0 := by
    apply Subtype.ext
    apply e.injective
    exact g.property.trans (map_zero e).symm
  have hcot (x : P.toExtension.Cotangent) : x = 0 := by
    obtain ⟨g, rfl⟩ := Algebra.Extension.Cotangent.mk_surjective x
    rw [hker g, map_zero]
  letI : Subsingleton P.toExtension.Cotangent := ⟨fun x y ↦ (hcot x).trans (hcot y).symm⟩
  let K := NaiveCotangent.Adic.naiveCotangent I P
  have hH (n : ℕ) (hn : n = 0 ∨ n = 1) : Subsingleton (K.homology n) := by
    apply ModuleCat.subsingleton_of_isZero
    apply (K.sc n).isZero_homology_of_isZero_X₂
    rcases hn with rfl | rfl
    · change CategoryTheory.Limits.IsZero (ModuleCat.of A (PEmpty → A))
      exact ModuleCat.isZero_of_subsingleton _
    · change CategoryTheory.Limits.IsZero (ModuleCat.of A P.toExtension.Cotangent)
      exact ModuleCat.isZero_of_subsingleton _
  refine
    { toTopologicallyFiniteType := ?_
      exists_pow_annihilates := ⟨0, PEmpty, inferInstance, P, ?_⟩ }
  · refine ⟨inferInstance, ?_⟩
    exact FiniteType.of_restrictScalars_finiteType A (A ⧸ I) _
  · intro a ha
    haveI := hH 1 (Or.inr rfl)
    haveI := hH 0 (Or.inl rfl)
    exact ⟨fun x ↦ Subsingleton.elim _ _, fun x ↦ Subsingleton.elim _ _⟩

/-- Rig-étaleness unpacks as topological finite type together with annihilation
of completed naive cotangent homology by some power of `I`. -/
theorem iff (I : Ideal A) (B : Type u) [CommRing B] [Algebra A B] :
    RigEtale I B ↔
      TopologicallyFiniteType I B ∧ ∃ c : ℕ, annihilatesNaiveCotangent I B c :=
  by
    constructor
    · intro h
      exact ⟨h.toTopologicallyFiniteType, h.exists_pow_annihilates⟩
    · rintro ⟨hfinite, hann⟩
      exact { toTopologicallyFiniteType := hfinite, exists_pow_annihilates := hann }

/-- A rig-étale algebra is topologically of finite type and has some power of
`I` annihilating completed naive cotangent homology. -/
theorem spec (I : Ideal A) (B : Type u) [CommRing B] [Algebra A B]
    [RigEtale I B] :
    TopologicallyFiniteType I B ∧ ∃ c : ℕ, annihilatesNaiveCotangent I B c :=
  ⟨RigEtale.toTopologicallyFiniteType, RigEtale.exists_pow_annihilates⟩

end RigEtale

end Algebra

namespace RingHom

variable {A B : Type u} [CommRing A] [CommRing B]
variable [TopologicalSpace A] [TopologicalSpace B]
variable [TopologicalRing.IsAdicRing A] [TopologicalRing.IsAdicRing B]
variable [IsNoetherianRing A] [IsNoetherianRing B]

/-- A continuous homomorphism of adic Noetherian topological rings is rig-étale
when `B` is rig-étale over `(A, I)` for some ideal of definition `I` of `A`
that induces the ambient topology on `B`. -/
class RigEtale (φ : A →+* B) : Prop extends Continuous φ where
  /-- There is an ideal of definition of `A` inducing the topology on `B` and
  making `B` rig-étale over `(A, I)` via `φ`. -/
  exists_idealOfDefinition :
    ∃ I : Ideal A,
      TopologicalRing.Ideal.IsIdealOfDefinition I ∧
        IsAdic (Ideal.map φ I) ∧
          @Algebra.RigEtale A _ I B _ φ.toAlgebra

namespace RigEtale

/-- The identity of an adic Noetherian topological ring is rig-étale. -/
instance id {A : Type u} [CommRing A] [TopologicalSpace A]
    [TopologicalRing.IsAdicRing A] [IsNoetherianRing A] :
    RigEtale (RingHom.id A) :=
  by
    refine ⟨continuous_id, ?_⟩
    obtain ⟨I, hI, hcomplete⟩ :=
      TopologicalRing.IsAdicRing.exists_ideal_isAdicComplete (R := A)
    exact ⟨I, TopologicalRing.Ideal.isIdealOfDefinition_of_isAdic hI, by
      simpa using hI, Algebra.RigEtale.id I⟩

/-- Rig-étaleness of a continuous homomorphism is equivalent to the existence of
an ideal of definition of `A` inducing the topology on `B` and making the
target rig-étale over the source. -/
theorem iff (φ : A →+* B) :
    RigEtale φ ↔
      Continuous φ ∧ φ.IsAdicHom ∧
        ∃ I : Ideal A,
          TopologicalRing.Ideal.IsIdealOfDefinition I ∧
            IsAdic (Ideal.map φ I) ∧
              @Algebra.RigEtale A _ I B _ φ.toAlgebra :=
  by
    constructor
    · intro h
      rcases h.exists_idealOfDefinition with ⟨I, hI, hmap, hrig⟩
      exact ⟨h.toContinuous, ⟨I, hI, hmap⟩, ⟨I, hI, hmap, hrig⟩⟩
    · rintro ⟨hcont, _, hex⟩
      exact { toContinuous := hcont, exists_idealOfDefinition := hex }

/-- Rig-étaleness may equivalently be tested on every ideal of definition. -/
theorem iff_forall_idealOfDefinition (φ : A →+* B) :
    RigEtale φ ↔
      Continuous φ ∧ φ.IsAdicHom ∧
        ∀ I : Ideal A, TopologicalRing.Ideal.IsIdealOfDefinition I →
          IsAdic (Ideal.map φ I) ∧
            @Algebra.RigEtale A _ I B _ φ.toAlgebra :=
  sorry

/-- A rig-étale homomorphism is an adic continuous map, topologically of finite
type, and annihilates completed naive cotangent homology for some ideal of
definition of `A` inducing the topology on `B`. -/
theorem spec (φ : A →+* B) [RingHom.RigEtale φ] :
    Continuous φ ∧ φ.IsAdicHom ∧
      ∃ I : Ideal A,
        TopologicalRing.Ideal.IsIdealOfDefinition I ∧
          IsAdic (Ideal.map φ I) ∧
            @Algebra.TopologicallyFiniteType A _ I B _ φ.toAlgebra ∧
              ∃ c : ℕ, @Algebra.annihilatesNaiveCotangent A _ I B _ φ.toAlgebra c :=
  by
    rcases RingHom.RigEtale.exists_idealOfDefinition (φ := φ) with
      ⟨I, hI, hmap, hrig⟩
    letI : Algebra A B := φ.toAlgebra
    letI : @Algebra.RigEtale A _ I B _ φ.toAlgebra := hrig
    have hspec := Algebra.RigEtale.spec I B
    exact ⟨RingHom.RigEtale.toContinuous, ⟨I, hI, hmap⟩,
      ⟨I, hI, hmap, hspec.1, hspec.2⟩⟩

end RigEtale

end RingHom
