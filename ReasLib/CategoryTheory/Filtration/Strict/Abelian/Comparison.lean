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
    IsIso (coimageImageComparison f).hom := sorry

namespace Graded

/-- The canonical factorization through filtered coimage and image remains the original map on
graded pieces. -/
theorem factorization
    (f : A ⟶ B) (p : ℤ) :
    gradedPieceMap (toCoimage f) p ≫ gradedPieceMap (coimageImageComparison f) p ≫
    gradedPieceMap (imageInclusion f) p = gradedPieceMap f p := sorry

namespace Kernel

/-- An isomorphism on the graded coimage-image comparison implies exactness of the graded
kernel row. -/
theorem exact_of_isIso
    (f : A ⟶ B) (p : ℤ) [IsIso (gradedPieceMap (coimageImageComparison f) p)] :
    (FilteredObject.Hom.Graded.Kernel.shortComplex f p).Exact := sorry

/-- Kernel-side graded exactness makes the graded coimage-image comparison monic. -/
theorem mono_of_exact
    (f : A ⟶ B) (p : ℤ)
    (hExact : (FilteredObject.Hom.Graded.Kernel.shortComplex f p).Exact) :
    Mono (gradedPieceMap (coimageImageComparison f) p) := sorry

end Kernel

namespace Cokernel

/-- An isomorphism on the graded coimage-image comparison implies exactness of the graded
cokernel row. -/
theorem exact_of_isIso
    (f : A ⟶ B) (p : ℤ) [IsIso (gradedPieceMap (coimageImageComparison f) p)] :
    (FilteredObject.Hom.Graded.Cokernel.shortComplex f p).Exact := sorry

/-- Cokernel-side graded exactness makes the graded coimage-image comparison epic. -/
theorem epi_of_exact
    (f : A ⟶ B) (p : ℤ)
    (hExact : (FilteredObject.Hom.Graded.Cokernel.shortComplex f p).Exact) :
    Epi (gradedPieceMap (coimageImageComparison f) p) := sorry

end Cokernel

/-- Kernel-side and cokernel-side exactness identify the graded coimage-image comparison as an
isomorphism. -/
theorem isIso_of_exact
    (f : A ⟶ B) (p : ℤ)
    (hKernel : (FilteredObject.Hom.Graded.Kernel.shortComplex f p).Exact)
    (hCokernel : (FilteredObject.Hom.Graded.Cokernel.shortComplex f p).Exact) :
    IsIso (gradedPieceMap (coimageImageComparison f) p) := sorry

/-- Degreewise kernel-side and cokernel-side exactness identify the associated-graded
coimage-image comparison as an isomorphism. -/
theorem associated_isIso_of_exact
    (f : A ⟶ B)
    (hKernel : ∀ p : ℤ, (FilteredObject.Hom.Graded.Kernel.shortComplex f p).Exact)
    (hCokernel : ∀ p : ℤ, (FilteredObject.Hom.Graded.Cokernel.shortComplex f p).Exact) :
    IsIso (associatedGradedMap (coimageImageComparison f)) := sorry

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
          (FilteredObject.Hom.Graded.Cokernel.shortComplex f p).Exact) := sorry

end Graded

end CoimageImageComparison

end FilteredObject.Hom

end CategoryTheory
