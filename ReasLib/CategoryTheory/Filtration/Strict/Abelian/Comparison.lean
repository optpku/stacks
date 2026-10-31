/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.ExactSequence
public import ReasLib.CategoryTheory.Filtration.Strict.Abelian.Graded

/-!
# Graded Exactness and the Coimage-Image Comparison

This file relates exactness of the canonical graded kernel and cokernel rows to the graded
coimage-image comparison.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

universe v u

noncomputable section

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace FilteredObject.Hom

open FilteredObject

variable [Abelian C]
variable {A B : FilteredObject C}

namespace CoimageImageComparison

/-- The underlying morphism of the filtered coimage-image comparison is an isomorphism. -/
theorem hom_isIso (f : A ⟶ B) :
    IsIso (coimageImageComparison f).hom := by
  let e := imageSubobjectIso f.hom ≪≫ (Abelian.imageIsoImage f.hom).symm
  change IsIso ((Abelian.coimageImageComparison f.hom ≫ e.inv) ≫ e.hom)
  rw [Category.assoc, e.inv_hom_id, Category.comp_id]
  infer_instance

namespace Graded

/-- The canonical factorization through filtered coimage and image remains the original map on
graded pieces. -/
theorem factorization
    (f : A ⟶ B) (p : ℤ) :
    gradedPieceMap (toCoimage f) p ≫ gradedPieceMap (coimageImageComparison f) p ≫
    gradedPieceMap (imageInclusion f) p = gradedPieceMap f p := by
  have hfac : toCoimage f ≫ coimageImageComparison f ≫ imageInclusion f = f := by
    apply FilteredObject.Hom.ext
    let e := imageSubobjectIso f.hom ≪≫ (Abelian.imageIsoImage f.hom).symm
    change Abelian.coimage.π f.hom ≫
      ((Abelian.coimageImageComparison f.hom ≫ e.inv) ≫ e.hom) ≫
        Abelian.image.ι f.hom = f.hom
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    exact Abelian.coimage_image_factorisation f.hom
  simpa only [gradedPieceMap_comp] using
    congrArg (fun g : A ⟶ B => gradedPieceMap g p) hfac

namespace Kernel

/-- An isomorphism on the graded coimage-image comparison implies exactness of the graded
kernel row. -/
theorem exact_of_isIso
    (f : A ⟶ B) (p : ℤ) [IsIso (gradedPieceMap (coimageImageComparison f) p)] :
    (FilteredObject.Hom.Graded.Kernel.shortComplex f p).Exact := by
  have hImage := FilteredObject.Hom.Graded.Image.shortExact f p
  haveI : Mono (gradedPieceMap (imageInclusion f) p) := hImage.mono_f
  let φ : FilteredObject.Hom.Graded.Coimage.shortComplex f p ⟶
      FilteredObject.Hom.Graded.Kernel.shortComplex f p :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := gradedPieceMap (coimageImageComparison f) p ≫
        gradedPieceMap (imageInclusion f) p
      comm₁₂ := by
        simp [FilteredObject.Hom.Graded.Coimage.shortComplex,
          FilteredObject.Hom.Graded.Kernel.shortComplex]
      comm₂₃ := by
        simpa [FilteredObject.Hom.Graded.Coimage.shortComplex,
          FilteredObject.Hom.Graded.Kernel.shortComplex] using (factorization f p).symm }
  haveI : Epi φ.τ₁ := inferInstanceAs (Epi (𝟙 ((kernel f).gradedPiece p)))
  haveI : IsIso φ.τ₂ := inferInstanceAs (IsIso (𝟙 (A.gradedPiece p)))
  haveI : Mono φ.τ₃ := mono_comp (gradedPieceMap (coimageImageComparison f) p)
    (gradedPieceMap (imageInclusion f) p)
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).1
    (FilteredObject.Hom.Graded.Coimage.shortExact f p).exact

/-- Kernel-side graded exactness makes the graded coimage-image comparison monic. -/
theorem mono_of_exact
    (f : A ⟶ B) (p : ℤ)
    (hExact : (FilteredObject.Hom.Graded.Kernel.shortComplex f p).Exact) :
    Mono (gradedPieceMap (coimageImageComparison f) p) := by
  have hCoimage := FilteredObject.Hom.Graded.Coimage.shortExact f p
  let h := hExact.rightHomologyDataOfIsColimitCokernelCofork _ hCoimage.gIsCokernel
  have heq : h.g' = gradedPieceMap (coimageImageComparison f) p ≫
      gradedPieceMap (imageInclusion f) p := by
    apply (cancel_epi h.p).1
    exact h.p_g'.trans (factorization f p).symm
  haveI : Mono (gradedPieceMap (coimageImageComparison f) p ≫
      gradedPieceMap (imageInclusion f) p) := heq ▸ hExact.mono_g' h
  exact mono_of_mono _ (gradedPieceMap (imageInclusion f) p)

end Kernel

namespace Cokernel

/-- An isomorphism on the graded coimage-image comparison implies exactness of the graded
cokernel row. -/
theorem exact_of_isIso
    (f : A ⟶ B) (p : ℤ) [IsIso (gradedPieceMap (coimageImageComparison f) p)] :
    (FilteredObject.Hom.Graded.Cokernel.shortComplex f p).Exact := by
  have hCoimage := FilteredObject.Hom.Graded.Coimage.shortExact f p
  haveI : Epi (gradedPieceMap (toCoimage f) p) := hCoimage.epi_g
  let φ : FilteredObject.Hom.Graded.Cokernel.shortComplex f p ⟶
      FilteredObject.Hom.Graded.Image.shortComplex f p :=
    { τ₁ := gradedPieceMap (toCoimage f) p ≫
        gradedPieceMap (coimageImageComparison f) p
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := by
        simpa [FilteredObject.Hom.Graded.Cokernel.shortComplex,
          FilteredObject.Hom.Graded.Image.shortComplex, Category.assoc] using factorization f p
      comm₂₃ := by
        simp [FilteredObject.Hom.Graded.Cokernel.shortComplex,
          FilteredObject.Hom.Graded.Image.shortComplex] }
  haveI : Epi φ.τ₁ := epi_comp (gradedPieceMap (toCoimage f) p)
    (gradedPieceMap (coimageImageComparison f) p)
  haveI : IsIso φ.τ₂ := inferInstanceAs (IsIso (𝟙 (B.gradedPiece p)))
  haveI : Mono φ.τ₃ := inferInstanceAs (Mono (𝟙 ((cokernel f).gradedPiece p)))
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2
    (FilteredObject.Hom.Graded.Image.shortExact f p).exact

/-- Cokernel-side graded exactness makes the graded coimage-image comparison epic. -/
theorem epi_of_exact
    (f : A ⟶ B) (p : ℤ)
    (hExact : (FilteredObject.Hom.Graded.Cokernel.shortComplex f p).Exact) :
    Epi (gradedPieceMap (coimageImageComparison f) p) := by
  have hImage := FilteredObject.Hom.Graded.Image.shortExact f p
  let h := hExact.leftHomologyDataOfIsLimitKernelFork _ hImage.fIsKernel
  have heq : h.f' = gradedPieceMap (toCoimage f) p ≫
      gradedPieceMap (coimageImageComparison f) p := by
    apply (cancel_mono h.i).1
    rw [h.f'_i]
    change gradedPieceMap f p =
      (gradedPieceMap (toCoimage f) p ≫ gradedPieceMap (coimageImageComparison f) p) ≫
        gradedPieceMap (imageInclusion f) p
    simpa only [Category.assoc] using (factorization f p).symm
  haveI : Epi (gradedPieceMap (toCoimage f) p ≫
      gradedPieceMap (coimageImageComparison f) p) := heq ▸ hExact.epi_f' h
  exact epi_of_epi (gradedPieceMap (toCoimage f) p) _

end Cokernel

/-- Kernel-side and cokernel-side exactness identify the graded coimage-image comparison as an
isomorphism. -/
theorem isIso_of_exact
    (f : A ⟶ B) (p : ℤ)
    (hKernel : (FilteredObject.Hom.Graded.Kernel.shortComplex f p).Exact)
    (hCokernel : (FilteredObject.Hom.Graded.Cokernel.shortComplex f p).Exact) :
    IsIso (gradedPieceMap (coimageImageComparison f) p) := by
  haveI := Kernel.mono_of_exact f p hKernel
  haveI := Cokernel.epi_of_exact f p hCokernel
  exact isIso_of_mono_of_epi _

/-- Degreewise kernel-side and cokernel-side exactness identify the associated-graded
coimage-image comparison as an isomorphism. -/
theorem associated_isIso_of_exact
    (f : A ⟶ B)
    (hKernel : ∀ p : ℤ, (FilteredObject.Hom.Graded.Kernel.shortComplex f p).Exact)
    (hCokernel : ∀ p : ℤ, (FilteredObject.Hom.Graded.Cokernel.shortComplex f p).Exact) :
    IsIso (associatedGradedMap (coimageImageComparison f)) := by
  letI : ∀ p : ℤ, IsIso (associatedGradedMap (coimageImageComparison f) p) :=
    fun p => isIso_of_exact f p (hKernel p) (hCokernel p)
  exact GradedObject.isIso_of_isIso_apply _

/-- The five-term graded exactness condition is equivalent to its two three-term exactness
conditions. -/
theorem fiveTermExact_iff (f : A ⟶ B) (p : ℤ) :
    (ComposableArrows.mk₅
      (0 : 0 ⟶ (kernel f).gradedPiece p)
      (gradedPieceMap (kernelι f) p)
      (gradedPieceMap f p)
      (gradedPieceMap (toCokernel f) p)
      (0 : (cokernel f).gradedPiece p ⟶ 0)).Exact ↔
        ((FilteredObject.Hom.Graded.Kernel.shortComplex f p).Exact ∧
          (FilteredObject.Hom.Graded.Cokernel.shortComplex f p).Exact) := by
  constructor
  · intro h
    exact ⟨h.exact 1, h.exact 2⟩
  · rintro ⟨hKernel, hCokernel⟩
    refine ⟨⟨?_⟩, ?_⟩
    · intro i hi
      have hi' : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
      rcases hi' with rfl | rfl | rfl | rfl
      · exact zero_comp
      · exact (FilteredObject.Hom.Graded.Kernel.shortComplex f p).zero
      · exact (FilteredObject.Hom.Graded.Cokernel.shortComplex f p).zero
      · exact comp_zero
    · intro i hi
      have hi' : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
      rcases hi' with rfl | rfl | rfl | rfl
      · exact (ShortComplex.exact_iff_mono _ rfl).2
          (FilteredObject.Hom.Graded.Kernel.mono f p)
      · exact hKernel
      · exact hCokernel
      · exact (ShortComplex.exact_iff_epi _ rfl).2
          (FilteredObject.Hom.Graded.Cokernel.epi f p)

end Graded

end CoimageImageComparison

end FilteredObject.Hom

end CategoryTheory
