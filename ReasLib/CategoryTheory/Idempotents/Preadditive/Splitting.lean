/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Idempotents.Preadditive

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoryTheory.Idempotents

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- An idempotent and its complement annihilate one another. -/
theorem comp_complement {X : C} (f : X ⟶ X) (hf : f ≫ f = f) :
    f ≫ (𝟙 X - f) = 0 ∧ (𝟙 X - f) ≫ f = 0 := by
  constructor <;> simp [Preadditive.comp_sub, Preadditive.sub_comp, hf]

/-- Factoring the complementary projector through the kernel gives a retraction
which is also a cokernel. No other kernels or cokernels are assumed. -/
theorem kernel_retraction_is_cokernel {X : C} (f : X ⟶ X) (hf : f ≫ f = f)
    [HasKernel f] (p : X ⟶ kernel f) (hp : p ≫ kernel.ι f = 𝟙 X - f) :
    kernel.ι f ≫ p = 𝟙 (kernel f) ∧
      ∃ h : f ≫ p = 0, Nonempty (IsColimit (CokernelCofork.ofπ p h)) := by
  have hip : kernel.ι f ≫ p = 𝟙 (kernel f) := by
    apply (cancel_mono (kernel.ι f)).1
    rw [Category.assoc, hp]
    simp
  have hfp : f ≫ p = 0 := by
    apply (cancel_mono (kernel.ι f)).1
    rw [Category.assoc, hp]
    simpa using (comp_complement f hf).1
  refine ⟨hip, hfp, ⟨?_⟩⟩
  refine CokernelCofork.IsColimit.ofπ p hfp (fun a _ ↦ kernel.ι f ≫ a) ?_ ?_
  · intro Z a ha
    rw [← Category.assoc, hp]
    simp [ha]
  · intro Z a ha m hm
    calc
      m = (kernel.ι f ≫ p) ≫ m := by rw [hip, Category.id_comp]
      _ = kernel.ι f ≫ a := by rw [Category.assoc, hm]

/-- Dually, factoring the complement through a cokernel gives a section which
is also a kernel. -/
theorem cokernel_section_is_kernel {X : C} (f : X ⟶ X) (hf : f ≫ f = f)
    [HasCokernel f] (i : cokernel f ⟶ X) (hi : cokernel.π f ≫ i = 𝟙 X - f) :
    i ≫ cokernel.π f = 𝟙 (cokernel f) ∧
      ∃ h : i ≫ f = 0, Nonempty (IsLimit (KernelFork.ofι i h)) := by
  have hip : i ≫ cokernel.π f = 𝟙 (cokernel f) := by
    apply (cancel_epi (cokernel.π f)).1
    rw [← Category.assoc, hi]
    simp
  have hif : i ≫ f = 0 := by
    apply (cancel_epi (cokernel.π f)).1
    rw [← Category.assoc, hi]
    simpa using (comp_complement f hf).2
  refine ⟨hip, hif, ⟨?_⟩⟩
  refine KernelFork.IsLimit.ofι i hif (fun a _ ↦ a ≫ cokernel.π f) ?_ ?_
  · intro Z a ha
    rw [Category.assoc, hi]
    simp [ha]
  · intro Z a ha m hm
    calc
      m = m ≫ (i ≫ cokernel.π f) := by rw [hip, Category.comp_id]
      _ = a ≫ cokernel.π f := by rw [← Category.assoc, hm]

/-- Factoring an idempotent through the kernel of its complement gives a retraction
which is also a cokernel of the complement. -/
theorem kernelComplementSplitting {X : C} (f : X ⟶ X) (hf : f ≫ f = f)
    [HasKernel (𝟙 X - f)] (q : X ⟶ kernel (𝟙 X - f))
    (hq : q ≫ kernel.ι (𝟙 X - f) = f) :
    kernel.ι (𝟙 X - f) ≫ q = 𝟙 (kernel (𝟙 X - f)) ∧
      ∃ h : (𝟙 X - f) ≫ q = 0,
        Nonempty (IsColimit (CokernelCofork.ofπ q h)) := by
  apply kernel_retraction_is_cokernel (𝟙 X - f) (idem_of_id_sub_idem f hf) q
  simpa only [sub_sub_cancel] using hq

/-- Factoring an idempotent through the cokernel of its complement gives a section
which is also a kernel of the complement. -/
theorem cokernelComplementSplitting {X : C} (f : X ⟶ X) (hf : f ≫ f = f)
    [HasCokernel (𝟙 X - f)] (j : cokernel (𝟙 X - f) ⟶ X)
    (hj : cokernel.π (𝟙 X - f) ≫ j = f) :
    j ≫ cokernel.π (𝟙 X - f) = 𝟙 (cokernel (𝟙 X - f)) ∧
      ∃ h : j ≫ (𝟙 X - f) = 0,
        Nonempty (IsLimit (KernelFork.ofι j h)) := by
  apply cokernel_section_is_kernel (𝟙 X - f) (idem_of_id_sub_idem f hf) j
  simpa only [sub_sub_cancel] using hj

private theorem exists_kernel_cokernel_splitting {X : C} (f : X ⟶ X)
    (hf : f ≫ f = f) (h : HasKernel f ∨ HasCokernel f) :
    ∃ (K : C) (i : K ⟶ X) (p : X ⟶ K),
      i ≫ p = 𝟙 K ∧ p ≫ i = 𝟙 X - f ∧
      ∃ (hi : i ≫ f = 0) (hp : f ≫ p = 0),
        Nonempty (IsLimit (KernelFork.ofι i hi)) ∧
        Nonempty (IsColimit (CokernelCofork.ofπ p hp)) := by
  rcases h with h | h
  · letI : HasKernel f := h
    let p := kernel.lift f (𝟙 X - f) (comp_complement f hf).2
    have hp : p ≫ kernel.ι f = 𝟙 X - f := kernel.lift_ι _ _ _
    rcases kernel_retraction_is_cokernel f hf p hp with ⟨hip, hfp, hc⟩
    exact ⟨kernel f, kernel.ι f, p, hip, hp, kernel.condition f, hfp,
      ⟨kernelIsKernel f⟩, hc⟩
  · letI : HasCokernel f := h
    let i := cokernel.desc f (𝟙 X - f) (comp_complement f hf).1
    have hi : cokernel.π f ≫ i = 𝟙 X - f := cokernel.π_desc _ _ _
    rcases cokernel_section_is_kernel f hf i hi with ⟨hip, hif, hk⟩
    exact ⟨cokernel f, i, cokernel.π f, hip, hi, hif, cokernel.condition f,
      hk, ⟨cokernelIsCokernel f⟩⟩

private theorem complementary_splittings_biproduct {X K L : C} (f : X ⟶ X)
    (i : K ⟶ X) (p : X ⟶ K) (j : L ⟶ X) (q : X ⟶ L)
    (hip : i ≫ p = 𝟙 K) (hjq : j ≫ q = 𝟙 L)
    (hpi : p ≫ i = 𝟙 X - f) (hqj : q ≫ j = f)
    (hi : i ≫ f = 0) (hj : j ≫ (𝟙 X - f) = 0) :
    ∃ (_ : HasBinaryBiproduct K L) (e : X ≅ K ⊞ L),
      i = biprod.inl ≫ e.inv ∧ p = e.hom ≫ biprod.fst ∧
      j = biprod.inr ≫ e.inv ∧ q = e.hom ≫ biprod.snd := by
  have hiq : i ≫ q = 0 := by
    calc
      i ≫ q = (i ≫ (q ≫ j)) ≫ q := by simp [Category.assoc, hjq]
      _ = 0 := by rw [hqj, hi, zero_comp]
  have hjp : j ≫ p = 0 := by
    calc
      j ≫ p = (j ≫ (p ≫ i)) ≫ p := by simp [Category.assoc, hip]
      _ = 0 := by rw [hpi, hj, zero_comp]
  let b : BinaryBicone K L :=
    { pt := X
      fst := p
      snd := q
      inl := i
      inr := j
      inl_fst := hip
      inl_snd := hiq
      inr_fst := hjp
      inr_snd := hjq }
  have htotal : b.fst ≫ b.inl + b.snd ≫ b.inr = 𝟙 b.pt := by
    change p ≫ i + q ≫ j = 𝟙 X
    rw [hpi, hqj, sub_add_cancel]
  letI : HasBinaryBiproduct K L := hasBinaryBiproduct_of_total b htotal
  refine ⟨‹HasBinaryBiproduct K L›,
    biprod.uniqueUpToIso K L (isBinaryBilimitOfTotal b htotal), ?_⟩
  simp [biprod.uniqueUpToIso, b]

/-- If each complementary idempotent has a kernel or a cokernel, both split.
The same first summand is a kernel and a cokernel of `f`, and the same second
summand is a kernel and a cokernel of its complement. Thus this single
biproduct realizes all four kernel/cokernel combinations. -/
theorem exists_biproduct_of_kernel_or_cokernel {X : C} (f : X ⟶ X)
    (hf : f ≫ f = f) (h₁ : HasKernel f ∨ HasCokernel f)
    (h₂ : HasKernel (𝟙 X - f) ∨ HasCokernel (𝟙 X - f)) :
    ∃ (K L : C) (_ : HasBinaryBiproduct K L) (e : X ≅ K ⊞ L)
      (i : K ⟶ X) (p : X ⟶ K) (j : L ⟶ X) (q : X ⟶ L),
      i = biprod.inl ≫ e.inv ∧ p = e.hom ≫ biprod.fst ∧
      j = biprod.inr ≫ e.inv ∧ q = e.hom ≫ biprod.snd ∧
      i ≫ p = 𝟙 K ∧ j ≫ q = 𝟙 L ∧ p ≫ i = 𝟙 X - f ∧ q ≫ j = f ∧
      ∃ (hi : i ≫ f = 0) (hp : f ≫ p = 0)
        (hj : j ≫ (𝟙 X - f) = 0) (hq : (𝟙 X - f) ≫ q = 0),
        Nonempty (IsLimit (KernelFork.ofι i hi)) ∧
        Nonempty (IsColimit (CokernelCofork.ofπ p hp)) ∧
        Nonempty (IsLimit (KernelFork.ofι j hj)) ∧
        Nonempty (IsColimit (CokernelCofork.ofπ q hq)) := by
  rcases exists_kernel_cokernel_splitting f hf h₁ with
    ⟨K, i, p, hip, hpi, hi, hp, hki, hcp⟩
  rcases exists_kernel_cokernel_splitting (𝟙 X - f) (idem_of_id_sub_idem f hf) h₂ with
    ⟨L, j, q, hjq, hqj, hj, hq, hkj, hcq⟩
  have hqj' : q ≫ j = f := by simpa only [sub_sub_cancel] using hqj
  rcases complementary_splittings_biproduct f i p j q hip hjq hpi hqj' hi hj with
    ⟨hb, e, hi_eq, hp_eq, hj_eq, hq_eq⟩
  exact ⟨K, L, hb, e, i, p, j, q, hi_eq, hp_eq, hj_eq, hq_eq,
    hip, hjq, hpi, hqj', hi, hp, hj, hq, hki, hcp, hkj, hcq⟩

/-- A section and retraction are respectively a kernel and a cokernel of the
complementary projector, in an arbitrary preadditive category. -/
theorem split_morphism_kernel_cokernel {X Y : C} (j : Y ⟶ X) (q : X ⟶ Y)
    (hj : j ≫ q = 𝟙 Y) :
    ∃ (hi : j ≫ (𝟙 X - q ≫ j) = 0) (hp : (𝟙 X - q ≫ j) ≫ q = 0),
      Nonempty (IsLimit (KernelFork.ofι j hi)) ∧
      Nonempty (IsColimit (CokernelCofork.ofπ q hp)) := by
  have hi : j ≫ (𝟙 X - q ≫ j) = 0 := by
    simp [← Category.assoc, hj]
  have hp : (𝟙 X - q ≫ j) ≫ q = 0 := by
    simp [Category.assoc, hj]
  refine ⟨hi, hp, ⟨?_⟩, ⟨?_⟩⟩
  · refine KernelFork.IsLimit.ofι j hi (fun a _ ↦ a ≫ q) ?_ ?_
    · intro Z a ha
      apply (sub_eq_zero.mp ?_).symm
      simpa only [Preadditive.comp_sub, Category.comp_id, Category.assoc] using ha
    · intro Z a ha m hm
      simpa [Category.assoc, hj] using congrArg (fun k ↦ k ≫ q) hm
  · refine CokernelCofork.IsColimit.ofπ q hp (fun a _ ↦ j ≫ a) ?_ ?_
    · intro Z a ha
      apply (sub_eq_zero.mp ?_).symm
      simpa only [Preadditive.sub_comp, Category.id_comp, Category.assoc] using ha
    · intro Z a ha m hm
      simpa [← Category.assoc, hj] using congrArg (fun k ↦ j ≫ k) hm

/-- A split pair extends to a biproduct as soon as its projector has a kernel
or a cokernel. The complementary summand is simultaneously both, and the
biproduct maps on the given summand are the original section and retraction. -/
theorem split_morphism_biproduct {X Y : C} (j : Y ⟶ X) (q : X ⟶ Y)
    (hj : j ≫ q = 𝟙 Y) (h : HasKernel (q ≫ j) ∨ HasCokernel (q ≫ j)) :
    ∃ (K : C) (_ : HasBinaryBiproduct K Y) (e : X ≅ K ⊞ Y)
      (i : K ⟶ X) (p : X ⟶ K),
      i = biprod.inl ≫ e.inv ∧ p = e.hom ≫ biprod.fst ∧
      j = biprod.inr ≫ e.inv ∧ q = e.hom ≫ biprod.snd ∧
      i ≫ p = 𝟙 K ∧ p ≫ i = 𝟙 X - q ≫ j ∧
      ∃ (hi : i ≫ (q ≫ j) = 0) (hp : (q ≫ j) ≫ p = 0),
        Nonempty (IsLimit (KernelFork.ofι i hi)) ∧
        Nonempty (IsColimit (CokernelCofork.ofπ p hp)) := by
  have hf : (q ≫ j) ≫ (q ≫ j) = q ≫ j := by
    rw [Category.assoc, ← Category.assoc j q j, hj, Category.id_comp]
  rcases exists_kernel_cokernel_splitting (q ≫ j) hf h with
    ⟨K, i, p, hip, hpi, hi, hp, hki, hcp⟩
  have hjf : j ≫ (𝟙 X - q ≫ j) = 0 := by simp [← Category.assoc, hj]
  rcases complementary_splittings_biproduct (q ≫ j) i p j q hip hj hpi rfl hi hjf with
    ⟨hb, e, hi_eq, hp_eq, hj_eq, hq_eq⟩
  exact ⟨K, hb, e, i, p, hi_eq, hp_eq, hj_eq, hq_eq, hip, hpi, hi, hp, hki, hcp⟩

end CategoryTheory.Idempotents
