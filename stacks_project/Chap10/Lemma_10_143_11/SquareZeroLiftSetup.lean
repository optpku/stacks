/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Ideal.CotangentBaseChange
public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.RingTheory.RingHom.Unramified
public import stacks_project.Chap10.Lemma_10_143_11.IdealAndCotangentMaps

@[expose] public section

-- Declarations moved out of `Lemma_10_143_11.lean` to keep the active proof file small.

open scoped TensorProduct

universe u v w x

namespace RingHom

section

variable {Aprime : Type u} {A : Type v} {Bprime : Type w} {B : Type x}
variable [CommRing Aprime] [CommRing A] [CommRing Bprime] [CommRing B]
variable (g : Aprime →+* Bprime) (qA : Aprime →+* A) (qB : Bprime →+* B) (f : A →+* B)

/-- Helper for Lemma 10.143.11: the mapped square-zero ideal acts trivially on the tensor model
`S ⊗[R] I/I²`. -/
lemma mapped_ideal_smul_tensor_cotangent_eq_zero
    {R : Type*} [CommRing R]
    {S : Type*} [CommRing S] [Algebra R S]
    (I : Ideal R) (x : Ideal.map (algebraMap R S) I)
    (m : S ⊗[R] I.Cotangent) :
    (x : S) • m = 0 := sorry

/-- Helper for Lemma 10.143.11: flat base change identifies `C ⊗[R] I/I²` with the cotangent
space of the extended ideal inside the raw tensor-product model `C ⊗[R] R`. -/
noncomputable def source_tensor_cotangent_equiv_of_flat
    {R : Type*} [CommRing R] {C : Type*} [CommRing C] [Algebra R C]
    (I : Ideal R) [Module.Flat R C] :
    C ⊗[R] I.Cotangent ≃ₗ[C]
      (Ideal.map
        (Algebra.TensorProduct.includeRight.toRingHom : R →+* C ⊗[R] R) I).Cotangent :=
  Ideal.tensorCotangentEquiv (R := R) (T := C) (I := I)

/-- Helper for Lemma 10.143.11: a surjective formally smooth algebra map has idempotent kernel. -/
lemma isIdempotentElem_ker_of_surjective_formally_smooth
    {R : Type*} [CommRing R] {S : Type*} [CommRing S] [Algebra R S]
    (hSurj : Function.Surjective (algebraMap R S))
    (hSmooth : Algebra.FormallySmooth R S) :
    IsIdempotentElem (RingHom.ker (algebraMap R S)) := by
  -- For surjective algebra maps, formal smoothness is exactly the idempotence of the kernel.
  exact (Algebra.FormallySmooth.iff_of_surjective hSurj).mp hSmooth

/-- Helper for Lemma 10.143.11: a surjective formally smooth algebra map whose kernel lies inside
a square-zero ideal is injective. -/
lemma injective_of_surjective_formally_smooth_of_ker_le_square_zero
    {R : Type*} [CommRing R] {S : Type*} [CommRing S] [Algebra R S]
    (hSurj : Function.Surjective (algebraMap R S))
    (hSmooth : Algebra.FormallySmooth R S)
    {J : Ideal R} (hker_le : RingHom.ker (algebraMap R S) ≤ J)
    (hJsq : J ^ 2 = ⊥) :
    Function.Injective (algebraMap R S) := by
  -- First collapse the kernel to zero using the formally-smooth idempotence criterion.
  have hker_idem : IsIdempotentElem (RingHom.ker (algebraMap R S)) :=
    isIdempotentElem_ker_of_surjective_formally_smooth hSurj hSmooth
  have hker_bot : RingHom.ker (algebraMap R S) = ⊥ :=
    eq_bot_of_isIdempotentElem_of_le_square_zero hker_idem hker_le hJsq
  intro x y hxy
  -- Equality of images means the difference lands in the zero kernel.
  have hsub : x - y ∈ RingHom.ker (algebraMap R S) := by
    rw [RingHom.mem_ker, map_sub, hxy]
    simp
  rw [hker_bot] at hsub
  exact sub_eq_zero.mp (by simpa using hsub)

/-- Helper for Lemma 10.143.11: the composite `Aprime → Bprime → B` is formally unramified,
because it identifies with the composition of the formally unramified maps `qA` and `f`. -/
lemma composite_formallyUnramified_of_surjective_square
    (hcomm : qB.comp g = f.comp qA)
    (hEtale : f.Etale)
    (hSurjA : Function.Surjective qA)
    (hSurjB : Function.Surjective qB) :
    (qB.comp g).FormallyUnramified := by
  have hqA : qA.FormallyUnramified := RingHom.FormallyUnramified.of_surjective hSurjA
  have _hqB : qB.FormallyUnramified := RingHom.FormallyUnramified.of_surjective hSurjB
  have hf : f.FormallyUnramified := hEtale.formallyUnramified
  -- Rewrite the composite square and then use stability under composition.
  rw [hcomm]
  exact RingHom.FormallyUnramified.comp hqA hf

/-- Helper for Lemma 10.143.11: a quotient map followed by the chosen quotient equivalence is
surjective and has the expected kernel. -/
lemma lifted_quotient_map_ker_eq_map
    {C : Type*} [CommRing C] (c : Aprime →+* C)
    (e : (C ⧸ Ideal.map c (ker qA)) ≃+* B) :
    Function.Surjective (e.toRingHom.comp (Ideal.Quotient.mk (Ideal.map c (ker qA)))) ∧
      RingHom.ker (e.toRingHom.comp (Ideal.Quotient.mk (Ideal.map c (ker qA)))) =
        Ideal.map c (ker qA) := by
  constructor
  · -- Surjectivity is inherited from the quotient map and the chosen target equivalence.
    intro b
    obtain ⟨x, rfl⟩ := e.surjective b
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    refine ⟨y, ?_⟩
    rfl
  · -- The quotient map has kernel exactly the quotient ideal, and the equivalence is injective.
    ext x
    rw [RingHom.mem_ker]
    constructor
    · intro hx
      have hx' : Ideal.Quotient.mk (Ideal.map c (ker qA)) x = 0 := by
        apply e.injective
        simpa using hx
      exact Ideal.Quotient.eq_zero_iff_mem.mp hx'
    · intro hx
      have hx' : Ideal.Quotient.mk (Ideal.map c (ker qA)) x = 0 := by
        exact Ideal.Quotient.eq_zero_iff_mem.mpr hx
      simpa using congrArg e hx'

/-- Helper for Lemma 10.143.11: the lifted étale structure map is formally smooth. -/
lemma lifted_etale_formally_smooth
    {C : Type*} [CommRing C] (c : Aprime →+* C)
    (hc : c.Etale) :
    c.FormallySmooth := by
  -- Étale maps are smooth, and smooth maps are formally smooth.
  have hcSmooth : c.Smooth :=
    (RingHom.etale_iff_formallyUnramified_and_smooth (f := c)).mp hc |>.2
  exact hcSmooth.formallySmooth

/-- Helper for Lemma 10.143.11: a square-zero ideal is nilpotent of exponent at most `2`. -/
lemma isNilpotent_of_square_zero
    {R : Type*} [CommRing R] (I : Ideal R) (hI : I ^ 2 = ⊥) :
    IsNilpotent I := by
  -- The source proof only needs nilpotence to invoke formal smoothness lifting.
  exact ⟨2, hI⟩


end

end RingHom
