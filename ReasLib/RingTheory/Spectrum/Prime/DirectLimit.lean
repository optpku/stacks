/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Colimit.Ring
public import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-!
# Inverse limits of prime spectra along directed ring systems

Compatible families of primes along a directed system of commutative rings
form the inverse limit of the sets `PrimeSpectrum (A i)`. This type is in
bijection with `PrimeSpectrum` of the directed colimit `Ring.DirectLimit`.
-/

@[expose] public section

universe u v

noncomputable section

namespace PrimeSpectrum

section InverseLimit

variable {ι : Type u} [Preorder ι]
variable (A : ι → Type v) [∀ i, CommRing (A i)]
variable (φ : ∀ i j, i ≤ j → A i →+* A j)

/-- A family of primes is compatible when each transition map pulls the later
prime back to the earlier one. -/
def IsCompatible (p : ∀ i, PrimeSpectrum (A i)) : Prop :=
  ∀ ⦃i j⦄ (hij : i ≤ j), comap (φ i j hij) (p j) = p i

/-- The inverse limit of the sets `PrimeSpectrum (A i)`, realized as compatible
families in the product. -/
def inverseLimit :=
  {p : ∀ i, PrimeSpectrum (A i) // IsCompatible A φ p}

/-- The component of a compatible family at the index `i`. -/
def proj (q : inverseLimit A φ) (i : ι) : PrimeSpectrum (A i) :=
  q.val i

/-- The component projection returns the underlying family at `i`. -/
theorem proj_apply (q : inverseLimit A φ) (i : ι) :
    proj A φ q i = q.val i := rfl

/-- Compatibility is equivalent to arising as the components of a point of the
inverse limit. -/
theorem mem_inverseLimit {p : ∀ i, PrimeSpectrum (A i)} :
    IsCompatible A φ p ↔ ∃ q : inverseLimit A φ, ∀ i, proj A φ q i = p i :=
  by
    constructor
    · intro hp
      exact ⟨⟨p, hp⟩, fun _ ↦ rfl⟩
    · rintro ⟨q, hq⟩
      have h : q.val = p := funext hq
      exact h ▸ q.property

/-- Two points of the inverse limit agree when all components agree. -/
theorem inverseLimit_ext {q q' : inverseLimit A φ}
    (h : ∀ i, proj A φ q i = proj A φ q' i) : q = q' :=
  Subtype.ext (funext h)

/-- The underlying family of a point of the inverse limit is compatible. -/
theorem isCompatible_proj (q : inverseLimit A φ) :
    IsCompatible A φ (fun i ↦ proj A φ q i) := q.property

end InverseLimit

section DirectLimit

variable {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
variable (A : ι → Type v) [∀ i, CommRing (A i)]
variable (φ : ∀ i j, i ≤ j → A i →+* A j)
variable [DirectedSystem A (φ · · ·)]

/-- Pulling a colimit prime back along the stage maps yields a compatible family. -/
theorem isCompatible_comap (p : PrimeSpectrum (Ring.DirectLimit A (φ · · ·))) :
    IsCompatible A φ (fun i ↦ comap (Ring.DirectLimit.of A (φ · · ·) i) p) :=
  by
    intro i j hij
    rw [← comap_comp_apply]
    congr 1
    ext x
    exact Ring.DirectLimit.of_f hij x

/-- The compatible family of pullbacks of a prime of the directed colimit. -/
def toInverseLimit (p : PrimeSpectrum (Ring.DirectLimit A (φ · · ·))) :
    inverseLimit A φ :=
  ⟨fun i ↦ comap (Ring.DirectLimit.of A (φ · · ·) i) p, isCompatible_comap A φ p⟩

/-- The `i`-component of the forward map is `comap` along the stage map from
`A i`. -/
theorem toInverseLimit_apply (p : PrimeSpectrum (Ring.DirectLimit A (φ · · ·)))
    (i : ι) :
    proj A φ (toInverseLimit A φ p) i =
      comap (Ring.DirectLimit.of A (φ · · ·) i) p := rfl

private theorem transition_mem_iff (q : inverseLimit A φ) {i j : ι}
    (hij : i ≤ j) (x : A i) :
    φ i j hij x ∈ (proj A φ q j).asIdeal ↔ x ∈ (proj A φ q i).asIdeal := by
  change x ∈ (comap (φ i j hij) (proj A φ q j)).asIdeal ↔ _
  rw [isCompatible_proj A φ q hij]

private theorem mem_proj_iff_of_of_eq (q : inverseLimit A φ) {i j : ι}
    (x : A i) (y : A j)
    (h : Ring.DirectLimit.of A (φ · · ·) i x = Ring.DirectLimit.of A (φ · · ·) j y) :
    x ∈ (proj A φ q i).asIdeal ↔ y ∈ (proj A φ q j).asIdeal := by
  have h' := congrArg (Ring.DirectLimit.ringEquiv A φ) h
  simp only [Ring.DirectLimit.ringEquiv_of] at h'
  obtain ⟨k, hik, hjk, hxy⟩ := Quotient.exact h'
  rw [← transition_mem_iff A φ q hik x, ← transition_mem_iff A φ q hjk y, hxy]

private theorem mem_iSup_map_iff (q : inverseLimit A φ)
    (z : Ring.DirectLimit A (φ · · ·)) :
    z ∈ (⨆ i, Ideal.map (Ring.DirectLimit.of A (φ · · ·) i) (proj A φ q i).asIdeal) ↔
      ∃ i x, x ∈ (proj A φ q i).asIdeal ∧ Ring.DirectLimit.of A (φ · · ·) i x = z := by
  let J : Ideal (Ring.DirectLimit A (φ · · ·)) :=
    { carrier := {z | ∃ i x, x ∈ (proj A φ q i).asIdeal ∧
          Ring.DirectLimit.of A (φ · · ·) i x = z}
      zero_mem' := by
        obtain ⟨i⟩ := ‹Nonempty ι›
        exact ⟨i, 0, (proj A φ q i).asIdeal.zero_mem, map_zero _⟩
      add_mem' := by
        rintro _ _ ⟨i, x, hx, rfl⟩ ⟨j, y, hy, rfl⟩
        obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
        refine ⟨k, φ i k hik x + φ j k hjk y, ?_, ?_⟩
        · exact (proj A φ q k).asIdeal.add_mem
            ((transition_mem_iff A φ q hik x).2 hx)
            ((transition_mem_iff A φ q hjk y).2 hy)
        · rw [map_add, Ring.DirectLimit.of_f, Ring.DirectLimit.of_f]
      smul_mem' := by
        rintro r _ ⟨i, x, hx, rfl⟩
        obtain ⟨j, y, rfl⟩ := Ring.DirectLimit.exists_of r
        obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
        refine ⟨k, φ j k hjk y * φ i k hik x, ?_, ?_⟩
        · exact (proj A φ q k).asIdeal.mul_mem_left _
            ((transition_mem_iff A φ q hik x).2 hx)
        · rw [map_mul, Ring.DirectLimit.of_f, Ring.DirectLimit.of_f]
          rfl }
  have hJ : (⨆ i, Ideal.map (Ring.DirectLimit.of A (φ · · ·) i)
      (proj A φ q i).asIdeal) = J := by
    apply le_antisymm
    · refine iSup_le fun i ↦ Ideal.map_le_iff_le_comap.2 ?_
      intro x hx
      exact ⟨i, x, hx, rfl⟩
    · rintro _ ⟨i, x, hx, rfl⟩
      exact Ideal.mem_iSup_of_mem i (Ideal.mem_map_of_mem _ hx)
  rw [hJ]
  rfl

private theorem of_mem_iSup_map_iff (q : inverseLimit A φ) (i : ι) (x : A i) :
    Ring.DirectLimit.of A (φ · · ·) i x ∈
        (⨆ j, Ideal.map (Ring.DirectLimit.of A (φ · · ·) j) (proj A φ q j).asIdeal) ↔
      x ∈ (proj A φ q i).asIdeal := by
  rw [mem_iSup_map_iff A φ q]
  constructor
  · rintro ⟨j, y, hy, hxy⟩
    exact (mem_proj_iff_of_of_eq A φ q y x hxy).1 hy
  · intro hx
    exact ⟨i, x, hx, rfl⟩

/-- The colimit prime whose underlying ideal is the directed union of the images
of a compatible family. For an empty index type, this is the zero prime of the
initial ring. -/
def ofInverseLimit {ι : Type u} [Preorder ι] [IsDirectedOrder ι]
    (A : ι → Type v) [∀ i, CommRing (A i)]
    (φ : ∀ i j, i ≤ j → A i →+* A j) [DirectedSystem A (φ · · ·)]
    (q : inverseLimit A φ) :
    PrimeSpectrum (Ring.DirectLimit A (φ · · ·)) where
  asIdeal := ⨆ i, Ideal.map (Ring.DirectLimit.of A (φ · · ·) i) (proj A φ q i).asIdeal
  isPrime := by
    classical
    cases isEmpty_or_nonempty ι with
    | inl h =>
      letI := h
      let f : Ring.DirectLimit A (φ · · ·) →+* ℤ :=
        Ring.DirectLimit.lift A (φ · · ·) ℤ (fun i ↦ isEmptyElim i)
          (fun i ↦ isEmptyElim i)
      have hf : Function.Injective f := by
        have hgf : (Int.castRingHom _).comp f = RingHom.id _ :=
          Ring.DirectLimit.hom_ext _ fun i ↦ isEmptyElim i
        exact (show Function.LeftInverse (Int.castRingHom _) f from
          fun x ↦ DFunLike.congr_fun hgf x).injective
      have hI : (⨆ i, Ideal.map (Ring.DirectLimit.of A (φ · · ·) i)
          (proj A φ q i).asIdeal) = ⊥ := by
        apply le_antisymm
        · exact iSup_le fun i ↦ isEmptyElim i
        · exact bot_le
      rw [hI, ← Ideal.comap_bot_of_injective f hf]
      infer_instance
    | inr h =>
      letI := h
      constructor
      · rw [Ideal.ne_top_iff_one]
        obtain ⟨i⟩ := h
        intro hmem
        have hmem' : Ring.DirectLimit.of A (φ · · ·) i 1 ∈
            (⨆ j, Ideal.map (Ring.DirectLimit.of A (φ · · ·) j)
              (proj A φ q j).asIdeal) := by
          simpa only [map_one] using hmem
        exact (proj A φ q i).isPrime.one_notMem
          ((of_mem_iSup_map_iff A φ q i 1).1 hmem')
      · intro x y hxy
        obtain ⟨i, x, rfl⟩ := Ring.DirectLimit.exists_of x
        obtain ⟨j, y, rfl⟩ := Ring.DirectLimit.exists_of y
        obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
        have hxy' : Ring.DirectLimit.of A (φ · · ·) k
            (φ i k hik x * φ j k hjk y) ∈
            (⨆ l, Ideal.map (Ring.DirectLimit.of A (φ · · ·) l)
              (proj A φ q l).asIdeal) := by
          simpa only [map_mul, Ring.DirectLimit.of_f] using hxy
        rcases (proj A φ q k).isPrime.mem_or_mem
            ((of_mem_iSup_map_iff A φ q k _).1 hxy') with hx | hy
        · exact Or.inl ((of_mem_iSup_map_iff A φ q i x).2
            ((transition_mem_iff A φ q hik x).1 hx))
        · exact Or.inr ((of_mem_iSup_map_iff A φ q j y).2
            ((transition_mem_iff A φ q hjk y).1 hy))

/-- The inverse map has underlying ideal the directed union of the images of the
components. -/
theorem ofInverseLimit_asIdeal (q : inverseLimit A φ) :
    (ofInverseLimit A φ q).asIdeal =
      ⨆ i, Ideal.map (Ring.DirectLimit.of A (φ · · ·) i) (proj A φ q i).asIdeal :=
  rfl

/-- The set bijection `Spec(colim A i) ≃ lim Spec(A i)` of compatible prime families. -/
def directLimitEquiv :
    PrimeSpectrum (Ring.DirectLimit A (φ · · ·)) ≃ inverseLimit A φ where
  toFun := toInverseLimit A φ
  invFun := ofInverseLimit A φ
  left_inv := by
    intro p
    apply PrimeSpectrum.ext
    apply Ideal.ext
    intro z
    obtain ⟨i, x, rfl⟩ := Ring.DirectLimit.exists_of z
    exact of_mem_iSup_map_iff A φ (toInverseLimit A φ p) i x
  right_inv := by
    intro q
    apply inverseLimit_ext
    intro i
    apply PrimeSpectrum.ext
    apply Ideal.ext
    intro x
    exact of_mem_iSup_map_iff A φ q i x

/-- The equivalence sends a colimit prime to the family of its pullbacks along
the stage maps. -/
theorem directLimitEquiv_apply (p : PrimeSpectrum (Ring.DirectLimit A (φ · · ·)))
    (i : ι) :
    proj A φ (directLimitEquiv A φ p) i =
      comap (Ring.DirectLimit.of A (φ · · ·) i) p := rfl

/-- The inverse equivalence reconstructs the directed-union prime. -/
theorem directLimitEquiv_symm_apply (q : inverseLimit A φ) :
    (directLimitEquiv A φ).symm q = ofInverseLimit A φ q := rfl

/-- The inverse equivalence has the same underlying ideal as `ofInverseLimit`. -/
theorem directLimitEquiv_symm_asIdeal (q : inverseLimit A φ) :
    ((directLimitEquiv A φ).symm q).asIdeal =
      ⨆ i, Ideal.map (Ring.DirectLimit.of A (φ · · ·) i) (proj A φ q i).asIdeal :=
  rfl

end DirectLimit

end PrimeSpectrum
