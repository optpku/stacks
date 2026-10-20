/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Strict.Abelian.CoimageImage

/-!
# Graded Exact Rows of Filtered Morphisms

This file owns the canonical graded kernel, coimage, image, and cokernel rows.  It separates the
degreewise exactness interface from the filtered constructions that supply those rows.
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

namespace Graded

namespace Kernel

/-- The graded row from the canonical kernel to the source and target of a filtered morphism. -/
def shortComplex (f : A ⟶ B) (p : ℤ) : ShortComplex C :=
  ShortComplex.mk (gradedPieceMap (kernelι f) p) (gradedPieceMap f p)
    (gradedPieceMap_comp_zero (kernelι f) f (kernelι_comp f) p)

/-- The canonical map from the graded kernel is monic. -/
theorem mono (f : A ⟶ B) (p : ℤ) :
    Mono (gradedPieceMap (kernelι f) p) := sorry

/-- The associated-graded map of the canonical filtered kernel inclusion is monic. -/
theorem associated_mono (f : A ⟶ B) :
    Mono (associatedGradedMap (kernelι f)) := sorry

/-- Exactness of the graded kernel row upgrades its left map to a chosen kernel. -/
noncomputable def isKernel
    (f : A ⟶ B) (p : ℤ) (hExact : (shortComplex f p).Exact) :
    IsLimit
      (KernelFork.ofι
        (gradedPieceMap (kernelι f) p)
        (gradedPieceMap_comp_zero (kernelι f) f (kernelι_comp f) p)) :=
  (((shortComplex f p).exact_and_mono_f_iff_f_is_kernel).1
    ⟨hExact, mono f p⟩).some

end Kernel

namespace Cokernel

/-- The graded row from the source and target to the canonical cokernel of a filtered morphism. -/
def shortComplex (f : A ⟶ B) (p : ℤ) : ShortComplex C :=
  ShortComplex.mk (gradedPieceMap f p) (gradedPieceMap (toCokernel f) p)
    (gradedPieceMap_comp_zero f (toCokernel f) (comp_toCokernel f) p)

/-- The canonical map to the graded cokernel is epic. -/
theorem epi (f : A ⟶ B) (p : ℤ) :
    Epi (gradedPieceMap (toCokernel f) p) := sorry

/-- The associated-graded map of the canonical filtered cokernel projection is epic. -/
theorem associated_epi (f : A ⟶ B) :
    Epi (associatedGradedMap (toCokernel f)) := sorry

/-- Exactness of the graded cokernel row upgrades its right map to a chosen cokernel. -/
noncomputable def isCokernel
    (f : A ⟶ B) (p : ℤ) (hExact : (shortComplex f p).Exact) :
    IsColimit
      (CokernelCofork.ofπ
        (gradedPieceMap (toCokernel f) p)
        (gradedPieceMap_comp_zero f (toCokernel f) (comp_toCokernel f) p)) :=
  (((shortComplex f p).exact_and_epi_g_iff_g_is_cokernel).1
    ⟨hExact, epi f p⟩).some

end Cokernel

namespace Coimage

/-- The graded row from the canonical kernel to the filtered coimage. -/
def shortComplex (f : A ⟶ B) (p : ℤ) : ShortComplex C :=
  ShortComplex.mk (gradedPieceMap (kernelι f) p) (gradedPieceMap (toCoimage f) p)
    (gradedPieceMap_comp_zero (kernelι f) (toCoimage f) (kernelι_comp_toCoimage f) p)

/-- The associated-graded kernel-coimage row is short exact in every degree. -/
@[stacks 05SP]
theorem shortExact (f : A ⟶ B) (p : ℤ) :
    (shortComplex f p).ShortExact := sorry

end Coimage

namespace Image

/-- The graded row from the filtered image to the canonical cokernel. -/
def shortComplex (f : A ⟶ B) (p : ℤ) : ShortComplex C :=
  ShortComplex.mk (gradedPieceMap (imageInclusion f) p) (gradedPieceMap (toCokernel f) p)
    (gradedPieceMap_comp_zero (imageInclusion f) (toCokernel f)
      (imageInclusion_comp_toCokernel f) p)

/-- The associated-graded image-cokernel row is short exact in every degree. -/
@[stacks 05SP]
theorem shortExact (f : A ⟶ B) (p : ℤ) :
    (shortComplex f p).ShortExact := sorry

end Image

end Graded

end FilteredObject.Hom

end CategoryTheory
