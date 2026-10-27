/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Strict.Abelian.CoimageImage
public import Mathlib.CategoryTheory.Abelian.CommSq

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

namespace Graded

/-- A zero composite of ambient morphisms induces a zero composite on graded pieces. -/
theorem gradedPieceMap_comp_zero_of_hom [HasZeroMorphisms C] [HasCokernels C]
    {A B D : FilteredObject C}
    (f : A ⟶ B) (g : B ⟶ D) (h : f.hom ≫ g.hom = 0) (p : ℤ) :
    gradedPieceMap f p ≫ gradedPieceMap g p = 0 := by
  have hstage : f.stageMap p ≫ g.stageMap p = 0 := by
    apply (cancel_mono (D.filtration.stage p).arrow).1
    simp only [Category.assoc, stageMap_arrow]
    rw [← Category.assoc, stageMap_arrow, Category.assoc, h, comp_zero, zero_comp]
  apply (cancel_epi (Limits.cokernel.π (A.filtration.succInclusion p))).1
  simp only [gradedPieceMap, Limits.cokernel.map, Limits.cokernel.π_desc,
    Limits.cokernel.π_desc_assoc, Category.assoc, comp_zero]
  rw [← Category.assoc, hstage, zero_comp]

variable [Abelian C]
variable {A B : FilteredObject C}

namespace Kernel

/-- The graded row from the canonical kernel to the source and target of a filtered morphism. -/
def shortComplex (f : A ⟶ B) (p : ℤ) : ShortComplex C :=
  ShortComplex.mk (gradedPieceMap (kernelι f) p) (gradedPieceMap f p)
    (gradedPieceMap_comp_zero_of_hom (kernelι f) f (kernelSubobject_arrow_comp f.hom) p)

/-- The canonical map from the graded kernel is monic. -/
theorem mono (f : A ⟶ B) (p : ℤ) :
    Mono (gradedPieceMap (kernelι f) p) := by
  have hstage (q : ℤ) :
      IsPullback ((kernelι f).stageMap q) ((kernel f).filtration q).arrow
        (A.filtration q).arrow (kernelSubobject f.hom).arrow := by
    have heq : (kernelι f).stageMap q =
        Subobject.pullbackπ (kernelSubobject f.hom).arrow (A.filtration q) := by
      apply (cancel_mono (A.filtration q).arrow).1
      exact (stageMap_arrow (kernelι f) q).trans
        (Subobject.isPullback (kernelSubobject f.hom).arrow (A.filtration q)).w.symm
    rw [heq]
    exact Subobject.isPullback (kernelSubobject f.hom).arrow (A.filtration q)
  have houter : IsPullback ((kernelι f).stageMap (p + 1))
      ((kernel f).filtration.succInclusion p ≫ ((kernel f).filtration.stage p).arrow)
      (A.filtration.succInclusion p ≫ (A.filtration.stage p).arrow)
      (kernelSubobject f.hom).arrow := by
    rw [DecreasingFiltration.succInclusion_arrow, DecreasingFiltration.succInclusion_arrow]
    exact hstage (p + 1)
  have hsquare := IsPullback.of_bot houter
    (succInclusion_naturality (kernelι f) p).symm (hstage p)
  exact Abelian.mono_cokernel_map_of_isPullback hsquare.flip

/-- The associated-graded map of the canonical filtered kernel inclusion is monic. -/
theorem associated_mono (f : A ⟶ B) :
    Mono (associatedGradedMap (kernelι f)) := sorry

/-- Exactness of the graded kernel row gives the canonical kernel universal property. -/
noncomputable def isKernel
    (f : A ⟶ B) (p : ℤ) (hExact : (shortComplex f p).Exact) :
    IsLimit
      (KernelFork.ofι
        (gradedPieceMap (kernelι f) p)
        (shortComplex f p).zero) := by
  letI : Mono (shortComplex f p).f := mono f p
  exact hExact.fIsKernel

end Kernel

namespace Cokernel

/-- The graded row from the source and target to the canonical cokernel of a filtered morphism. -/
def shortComplex (f : A ⟶ B) (p : ℤ) : ShortComplex C :=
  ShortComplex.mk (gradedPieceMap f p) (gradedPieceMap (toCokernel f) p)
    (gradedPieceMap_comp_zero_of_hom f (toCokernel f) (Limits.cokernel.condition f.hom) p)

/-- The canonical map to the graded cokernel is epic. -/
theorem epi (f : A ⟶ B) (p : ℤ) :
    Epi (gradedPieceMap (toCokernel f) p) := by
  let fac := Subobject.imageFactorisation (Limits.cokernel.π f.hom) (B.filtration p)
  have hepi : Epi fac.F.e := by
    change Epi (factorThruImage ((B.filtration p).arrow ≫ Limits.cokernel.π f.hom) ≫
      (Subobject.existsIsoImage (Limits.cokernel.π f.hom) (B.filtration p)).inv)
    infer_instance
  have heq : (toCokernel f).stageMap p = fac.F.e := by
    apply (cancel_mono ((cokernel f).filtration p).arrow).1
    exact (stageMap_arrow (toCokernel f) p).trans fac.F.fac.symm
  have : Epi ((toCokernel f).stageMap p) := heq.symm ▸ hepi
  change Epi (Limits.cokernel.desc _
    ((toCokernel f).stageMap p ≫ Limits.cokernel.π _) _)
  infer_instance

/-- The associated-graded map of the canonical filtered cokernel projection is epic. -/
theorem associated_epi (f : A ⟶ B) :
    Epi (associatedGradedMap (toCokernel f)) := sorry

/-- Exactness of the graded cokernel row gives the canonical cokernel universal property. -/
noncomputable def isCokernel
    (f : A ⟶ B) (p : ℤ) (hExact : (shortComplex f p).Exact) :
    IsColimit
      (CokernelCofork.ofπ
        (gradedPieceMap (toCokernel f) p)
        (shortComplex f p).zero) := by
  letI : Epi (shortComplex f p).g := epi f p
  exact hExact.gIsCokernel

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
