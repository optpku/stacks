/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.RingTheory.Noetherian.Basic
public import ReasLib.RingTheory.Topology.Adic.Complete
public import ReasLib.RingTheory.Topology.Adic.Hom
public import ReasLib.RingTheory.AdicCompletion.TopologicallyFiniteType
public import ReasLib.RingTheory.AdicCompletion.NaiveCotangent

/-!
# Rig-smooth algebras and continuous homomorphisms

An algebra over a Noetherian pair `(A, I)` is rig-smooth when it is
topologically of finite type and some power of `I` annihilates
`Ext¹_B(NL_{B/A}^∧, N)` for every `B`-module `N`. A continuous homomorphism of
adic Noetherian topological rings is rig-smooth when this holds for some,
equivalently any, ideal of definition of `A` that also induces the ambient
topology on `B`.
-/

@[expose] public section

universe u

namespace Algebra

variable {A : Type u} [CommRing A]

/-- Some power `I ^ c` annihilates `Ext¹_B(NL_{B/A}^∧, N)` for every
`B`-module `N`, computed from a finite completed presentation as the cokernel
of `Hom(⊕ᵢ B dx_i, N) → Hom(J / J², N)`. -/
def annihilatesExt1NaiveCotangent (I : Ideal A) (B : Type u) [CommRing B]
    [Algebra A B] (c : ℕ) : Prop :=
  ∃ (ι : Type u) (_ : Fintype ι) (P : NaiveCotangent.Adic.Presentation A B I ι),
    ∀ (N : Type u) [AddCommGroup N] [Module B N],
      ∀ a ∈ I ^ c,
        ∀ f : P.toExtension.Cotangent →ₗ[B] N,
          ∃ k : (ι → B) →ₗ[B] N,
            ∀ x : P.toExtension.Cotangent,
              (algebraMap A B a) • f x = k (NaiveCotangent.Adic.jacobian P x)

/-- Annihilation of `Ext¹` of the completed naive cotangent complex unpacks as
the existence of a finite presentation whose Jacobian cokernels on Hom-spaces
are killed by every element of `I ^ c`. -/
theorem annihilatesExt1NaiveCotangent_iff (I : Ideal A) (B : Type u) [CommRing B]
    [Algebra A B] (c : ℕ) :
    annihilatesExt1NaiveCotangent I B c ↔
      ∃ (ι : Type u) (_ : Fintype ι) (P : NaiveCotangent.Adic.Presentation A B I ι),
        ∀ (N : Type u) [AddCommGroup N] [Module B N],
          ∀ a ∈ I ^ c,
            ∀ f : P.toExtension.Cotangent →ₗ[B] N,
              ∃ k : (ι → B) →ₗ[B] N,
                ∀ x : P.toExtension.Cotangent,
                  (algebraMap A B a) • f x =
                    k (NaiveCotangent.Adic.jacobian P x) :=
  Iff.rfl

/-- An `A`-algebra `B` is rig-smooth over the pair `(A, I)` when it is
topologically of finite type and some power of `I` annihilates
`Ext¹_B(NL_{B/A}^∧, N)` for every `B`-module `N`. -/
class RigSmooth (I : Ideal A) (B : Type u) [CommRing B] [Algebra A B] : Prop
    extends TopologicallyFiniteType I B where
  /-- Some power of `I` annihilates `Ext¹` of the completed naive cotangent
  complex. -/
  exists_pow_annihilates_ext1 : ∃ c : ℕ, annihilatesExt1NaiveCotangent I B c

namespace RigSmooth

/-- The identity algebra is rig-smooth over `(A, I)` whenever `A` is `I`-adically
complete. -/
instance id (I : Ideal A) [IsAdicComplete I A] : RigSmooth I A := by
  classical
  refine
    { isAdicComplete := inferInstance
      finiteType_quotient := ?_
      exists_pow_annihilates_ext1 := ?_ }
  · apply FiniteType.of_surjective
      (Algebra.ofId (A ⧸ I) (A ⧸ I.map (algebraMap A A)))
    intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨Ideal.Quotient.mk I a, rfl⟩
  · let e := MvPolynomial.isEmptyAlgEquiv A PEmpty.{u + 1}
    letI : IsAdicComplete (NaiveCotangent.Adic.polynomialIdeal A I PEmpty.{u + 1})
        (MvPolynomial PEmpty.{u + 1} A) := by
      have hmap : I.map e.symm.toRingEquiv =
          NaiveCotangent.Adic.polynomialIdeal A I PEmpty.{u + 1} := by
        rw [← Ideal.map_coe]
        change I.map e.symm.toRingHom = I.map MvPolynomial.C
        rw [show e.symm.toRingHom = MvPolynomial.C from
          MvPolynomial.isEmptyAlgEquiv_symm_toRingHom A]
      exact hmap ▸ (IsAdicComplete.congr_ringEquiv I e.symm.toRingEquiv).mpr
        (inferInstance : IsAdicComplete I A)
    let e' : NaiveCotangent.Adic.polynomialCompletion A I PEmpty.{u + 1} ≃ₐ[A] A :=
      ((AdicCompletion.ofAlgEquiv
        (NaiveCotangent.Adic.polynomialIdeal A I PEmpty.{u + 1})).symm.restrictScalars A).trans e
    let P : NaiveCotangent.Adic.Presentation A A I PEmpty.{u + 1} :=
      ⟨e'.toAlgHom, e'.surjective⟩
    refine ⟨0, PEmpty.{u + 1}, inferInstance, P, ?_⟩
    intro N _ _ a _ f
    refine ⟨0, ?_⟩
    intro x
    -- The conormal module vanishes because the presentation map is injective.
    have hx : x = 0 := by
      obtain ⟨y, rfl⟩ := Algebra.Extension.Cotangent.mk_surjective x
      have hy := y.property
      change e' y.val = 0 at hy
      have hy0 : y = 0 := Subtype.ext (e'.injective (hy.trans (map_zero e').symm))
      rw [hy0, map_zero]
    simp [hx]

/-- Rig-smoothness unpacks as topological finite type together with annihilation
of `Ext¹` of the completed naive cotangent complex by some power of `I`. -/
theorem iff (I : Ideal A) (B : Type u) [CommRing B] [Algebra A B] :
    RigSmooth I B ↔
      TopologicallyFiniteType I B ∧
        ∃ c : ℕ, annihilatesExt1NaiveCotangent I B c :=
  ⟨fun h ↦ ⟨h.toTopologicallyFiniteType, h.exists_pow_annihilates_ext1⟩,
    fun h ↦ { toTopologicallyFiniteType := h.1, exists_pow_annihilates_ext1 := h.2 }⟩

/-- A rig-smooth algebra is topologically of finite type and has some power of
`I` annihilating `Ext¹` of the completed naive cotangent complex. -/
theorem spec (I : Ideal A) (B : Type u) [CommRing B] [Algebra A B]
    [RigSmooth I B] :
    TopologicallyFiniteType I B ∧ ∃ c : ℕ, annihilatesExt1NaiveCotangent I B c :=
  (iff I B).mp inferInstance

end RigSmooth

end Algebra

namespace RingHom

variable {A B : Type u} [CommRing A] [CommRing B]
variable [TopologicalSpace A] [TopologicalSpace B]
variable [TopologicalRing.IsAdicRing A] [TopologicalRing.IsAdicRing B]
variable [IsNoetherianRing A] [IsNoetherianRing B]

/-- A continuous homomorphism of adic Noetherian topological rings is rig-smooth
when `B` is rig-smooth over `(A, I)` for some ideal of definition `I` of `A`
that induces the ambient topology on `B`. -/
class RigSmooth (φ : A →+* B) : Prop extends Continuous φ where
  /-- There is an ideal of definition of `A` inducing the topology on `B` and
  making `B` rig-smooth over `(A, I)` via `φ`. -/
  exists_idealOfDefinition :
    ∃ I : Ideal A,
      TopologicalRing.Ideal.IsIdealOfDefinition I ∧
        IsAdic (Ideal.map φ I) ∧
          @Algebra.RigSmooth A _ I B _ φ.toAlgebra

namespace RigSmooth

/-- The identity of an adic Noetherian topological ring is rig-smooth. -/
instance id {A : Type u} [CommRing A] [TopologicalSpace A]
    [TopologicalRing.IsAdicRing A] [IsNoetherianRing A] :
    RigSmooth (RingHom.id A) := by
  obtain ⟨I, hI, hcomplete⟩ :=
    TopologicalRing.IsAdicRing.exists_ideal_isAdicComplete (R := A)
  have hdef : TopologicalRing.Ideal.IsIdealOfDefinition I := by
    obtain ⟨hopen, hcofinal⟩ := isAdic_iff.mp hI
    exact ⟨by simpa only [pow_one] using hopen 1, hcofinal⟩
  letI := hcomplete
  refine ⟨continuous_id, I, hdef, ?_, ?_⟩
  · simpa only [Ideal.map_id] using hI
  · exact Algebra.RigSmooth.id I

/-- Rig-smoothness of a continuous homomorphism is equivalent to the existence of
an ideal of definition of `A` inducing the topology on `B` and making the
target rig-smooth over the source. -/
theorem iff (φ : A →+* B) :
    RigSmooth φ ↔
      Continuous φ ∧ φ.IsAdicHom ∧
        ∃ I : Ideal A,
          TopologicalRing.Ideal.IsIdealOfDefinition I ∧
            IsAdic (Ideal.map φ I) ∧
              @Algebra.RigSmooth A _ I B _ φ.toAlgebra := by
  constructor
  · intro h
    obtain ⟨I, hI, hmap, hrig⟩ := h.exists_idealOfDefinition
    exact ⟨h.toContinuous, ⟨I, hI, hmap⟩, I, hI, hmap, hrig⟩
  · rintro ⟨hcont, _, hI⟩
    exact ⟨hcont, hI⟩

/-- Rig-smoothness may equivalently be tested on every ideal of definition. -/
theorem iff_forall_idealOfDefinition (φ : A →+* B) :
    RigSmooth φ ↔
      Continuous φ ∧ φ.IsAdicHom ∧
        ∀ I : Ideal A, TopologicalRing.Ideal.IsIdealOfDefinition I →
          IsAdic (Ideal.map φ I) ∧
            @Algebra.RigSmooth A _ I B _ φ.toAlgebra :=
  sorry

/-- A rig-smooth homomorphism is an adic continuous map, topologically of finite
type, and annihilates `Ext¹` of the completed naive cotangent complex for some
ideal of definition of `A` inducing the topology on `B`. -/
theorem spec (φ : A →+* B) [RingHom.RigSmooth φ] :
    Continuous φ ∧ φ.IsAdicHom ∧
      ∃ I : Ideal A,
        TopologicalRing.Ideal.IsIdealOfDefinition I ∧
          IsAdic (Ideal.map φ I) ∧
            @Algebra.TopologicallyFiniteType A _ I B _ φ.toAlgebra ∧
              ∃ c : ℕ,
                @Algebra.annihilatesExt1NaiveCotangent A _ I B _ φ.toAlgebra c := by
  obtain ⟨hcont, hadic, I, hI, hmap, hrig⟩ := (iff φ).mp inferInstance
  exact ⟨hcont, hadic, I, hI, hmap, hrig.toTopologicallyFiniteType,
    hrig.exists_pow_annihilates_ext1⟩

end RigSmooth

end RingHom
