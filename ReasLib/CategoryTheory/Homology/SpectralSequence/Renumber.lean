/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.Embedding.RestrictionHomology
public import Mathlib.Algebra.Homology.SpectralSequence.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Homology.SpectralSequence.Bounded

/-!
# Renumbering Cohomological Spectral Sequences

This file owns the standard simultaneous page and bidegree renumbering
`E'_r^{i,j} = E_{r-1}^{-j,i+2j}`.  The affine bidegree equivalence carries the old differential
of degree `(r - 1, 2 - r)` to the new differential of degree `(r, 1 - r)`, so a sequence
starting at `E₁` produces one starting at `E₂`.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace CategoryTheory
namespace CohomologicalSpectralSequence

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace Renumber

/-- The forward bidegree map used by the standard renumbering. -/
def bidegree (ij : ℤ × ℤ) : ℤ × ℤ :=
  (-ij.2, ij.1 + 2 * ij.2)

/-- The inverse bidegree map used by the standard renumbering. -/
def inverseBidegree (pq : ℤ × ℤ) : ℤ × ℤ :=
  (pq.2 + 2 * pq.1, -pq.1)

/-- The displayed inverse formula is a left inverse to the standard bidegree renumbering. -/
theorem inverseBidegree_bidegree (ij : ℤ × ℤ) :
    inverseBidegree (bidegree ij) = ij := sorry

/-- The displayed inverse formula is a right inverse to the standard bidegree renumbering. -/
theorem bidegree_inverseBidegree (pq : ℤ × ℤ) :
    bidegree (inverseBidegree pq) = pq := sorry

/-- The bidegree `(i,j)` of the renumbered spectral sequence corresponds to the old bidegree
`(-j,i+2j)`. -/
@[stacks 0G1Y "renumbering bidegree equivalence", stacks 0G20]
def bidegreeEquiv : (ℤ × ℤ) ≃ (ℤ × ℤ) where
  toFun := bidegree
  invFun := inverseBidegree
  left_inv := inverseBidegree_bidegree
  right_inv := bidegree_inverseBidegree

/-- Evaluation of the standard bidegree renumbering. -/
@[simp]
theorem bidegreeEquiv_apply (i j : ℤ) :
    bidegreeEquiv (i, j) = (-j, i + 2 * j) := sorry

/-- Evaluation of the inverse bidegree renumbering. -/
@[simp]
theorem bidegreeEquiv_symm_apply (p q : ℤ) :
    bidegreeEquiv.symm (p, q) = (q + 2 * p, -p) := sorry

/-- The complex shape on the new page `r`. -/
abbrev newShape (r : ℤ) : ComplexShape (ℤ × ℤ) :=
  ComplexShape.up' (⟨r, 1 - r⟩ : ℤ × ℤ)

/-- The old complex shape corresponding to the new page `r`. -/
abbrev oldShape (r : ℤ) : ComplexShape (ℤ × ℤ) :=
  ComplexShape.up' (⟨r - 1, 1 - (r - 1)⟩ : ℤ × ℤ)

/-- The standard bidegree equivalence identifies the new page-`r` differential shape with the
old page-`r-1` differential shape. -/
theorem shape_rel_iff (r : ℤ) (ij ij' : ℤ × ℤ) :
    (newShape r).Rel ij ij' ↔
      (oldShape r).Rel (bidegreeEquiv ij) (bidegreeEquiv ij') := sorry

/-- The complex-shape embedding underlying the standard spectral-sequence renumbering. -/
@[stacks 0G1Y "renumbering page-shape embedding", stacks 0G20]
def pageEmbedding (r : ℤ) :
    (newShape r).Embedding (oldShape r) :=
  ComplexShape.Embedding.mk' (newShape r) (oldShape r)
    bidegreeEquiv bidegreeEquiv.injective (shape_rel_iff r)

/-- The standard page-shape embedding preserves and reflects the differential relation. -/
instance pageEmbedding_isRelIff (r : ℤ) :
    (pageEmbedding r).IsRelIff := sorry

/-- The bidegree map underlying `pageEmbedding`. -/
@[simp]
theorem pageEmbedding_f (r : ℤ) (ij : ℤ × ℤ) :
    (pageEmbedding r).f ij = bidegreeEquiv ij := sorry

/-- The standard bidegree renumbering commutes with the predecessor operation on page shapes. -/
theorem pageEmbedding_prev (r : ℤ) (ij : ℤ × ℤ) :
    (pageEmbedding r).f ((newShape r).prev ij) =
      (oldShape r).prev (bidegreeEquiv ij) := sorry

/-- The standard bidegree renumbering commutes with the successor operation on page shapes. -/
theorem pageEmbedding_next (r : ℤ) (ij : ℤ × ℤ) :
    (pageEmbedding r).f ((newShape r).next ij) =
      (oldShape r).next (bidegreeEquiv ij) := sorry

/-- A new page `r ≥ 2` corresponds to a defined old page `r - 1 ≥ 1`. -/
theorem one_le_priorPage (r : ℤ) (hr : 2 ≤ r) : 1 ≤ r - 1 := sorry

/-- A page threshold at least one becomes at least two after the standard successor shift. -/
@[stacks 0G1Y "page bound after the standard renumbering", stacks 0G20]
theorem two_le_pageSucc {r : ℤ} (hr : 1 ≤ r) : 2 ≤ r + 1 := sorry

/-- Successive new pages correspond to successive old pages. -/
theorem priorPage_succ {r r' : ℤ} (hrr' : r + 1 = r') :
    r - 1 + 1 = r' - 1 := sorry

/-- The successor of a page at least two is again at least two. -/
theorem two_le_nextPage {r r' : ℤ} (hr : 2 ≤ r) (hrr' : r + 1 = r') :
    2 ≤ r' := sorry

/-- The page obtained by restricting old page `r - 1` along the standard bidegree
renumbering. -/
abbrev page (E : CohomologicalSpectralSequence C 1) (r : ℤ) (hr : 2 ≤ r) :
    HomologicalComplex C (newShape r) :=
  (E.page (r - 1) (one_le_priorPage r hr)).restriction (pageEmbedding r)

/-- The homology of a renumbered page is the following renumbered page. -/
noncomputable def pageHomologyIso (E : CohomologicalSpectralSequence C 1)
    (r r' : ℤ) (hrr' : r + 1 = r') (hr : 2 ≤ r) (ij : ℤ × ℤ) :
    (page E r hr).homology ij ≅
      (page E r' (two_le_nextPage hr hrr')).X ij :=
  ((E.page (r - 1) (one_le_priorPage r hr)).restrictionHomologyIso
      (pageEmbedding r) ((newShape r).prev ij) ij ((newShape r).next ij)
      rfl rfl (pageEmbedding_prev r ij) (pageEmbedding_f r ij)
      (pageEmbedding_next r ij) rfl rfl) ≪≫
    E.iso (r - 1) (r' - 1) (bidegreeEquiv ij)
      (priorPage_succ hrr') (one_le_priorPage r hr)

end Renumber

/-- Renumber a cohomological spectral sequence beginning at `E₁` by
`E'_r^{i,j} = E_{r-1}^{-j,i+2j}`.  The result begins at `E₂`. -/
@[stacks 0G1Y "page and bidegree renumbering", stacks 0G20]
noncomputable def renumber (E : CohomologicalSpectralSequence C 1) :
    E₂CohomologicalSpectralSequence C where
  page r hr := Renumber.page E r hr
  iso r r' ij hrr' hr := Renumber.pageHomologyIso E r r' hrr' hr ij

/-- The page of the canonical renumbering is the restriction of the preceding old page along
the standard bidegree embedding. -/
@[simp]
theorem renumber_page (E : CohomologicalSpectralSequence C 1)
    (r : ℤ) (hr : 2 ≤ r) :
    (renumber E).page r hr = Renumber.page E r hr := sorry

/-- A spectral sequence beginning at `E₂` is a renumbering of `E` when it is isomorphic to the
canonical simultaneous page and bidegree renumbering. -/
@[stacks 0G1Y "spectral-sequence renumbering relation", stacks 0G20]
def IsRenumbering (E : CohomologicalSpectralSequence C 1)
    (E' : E₂CohomologicalSpectralSequence C) : Prop :=
  Nonempty (E' ≅ renumber E)

/-- The canonical renumbering is a renumbering of its input spectral sequence. -/
theorem isRenumbering_renumber (E : CohomologicalSpectralSequence C 1) :
    IsRenumbering E (renumber E) := sorry

/-- A specified isomorphism with the canonical renumbering witnesses the renumbering relation. -/
theorem IsRenumbering.of_iso {E : CohomologicalSpectralSequence C 1}
    {E' : E₂CohomologicalSpectralSequence C} (e : E' ≅ renumber E) :
    IsRenumbering E E' := sorry

namespace Renumber

/-- A specified isomorphism `E' ≅ renumber E` identifies every new page with the restriction of
the preceding old page along the standard bidegree equivalence.  For `E' = renumber E` and the
identity isomorphism this is the identity of `Renumber.page E r hr`. -/
@[stacks 0G1Y "page comparison for a renumbering", stacks 0G20]
noncomputable def pageIso {E : CohomologicalSpectralSequence C 1}
    {E' : E₂CohomologicalSpectralSequence C} (e : E' ≅ renumber E)
    (r : ℤ) (hr : 2 ≤ r) :
    E'.page r hr ≅ page E r hr :=
  (SpectralSequence.pageFunctor C (fun r => ComplexShape.up' (⟨r, 1 - r⟩ : ℤ × ℤ)) 2 r hr).mapIso e

/-- The forward page comparison is the page component of the specified isomorphism. -/
@[simp]
theorem pageIso_hom {E : CohomologicalSpectralSequence C 1}
    {E' : E₂CohomologicalSpectralSequence C} (e : E' ≅ renumber E)
    (r : ℤ) (hr : 2 ≤ r) :
    (pageIso e r hr).hom = e.hom.hom r hr := sorry

/-- The inverse page comparison is the page component of the inverse isomorphism. -/
@[simp]
theorem pageIso_inv {E : CohomologicalSpectralSequence C 1}
    {E' : E₂CohomologicalSpectralSequence C} (e : E' ≅ renumber E)
    (r : ℤ) (hr : 2 ≤ r) :
    (pageIso e r hr).inv = e.inv.hom r hr := sorry

/-- For the canonical renumbering itself, the page comparison of the identity is the identity. -/
@[simp]
theorem pageIso_refl (E : CohomologicalSpectralSequence C 1) (r : ℤ) (hr : 2 ≤ r) :
    pageIso (Iso.refl (renumber E)) r hr = Iso.refl (page E r hr) := sorry

/-- Entrywise form of the standard renumbering formula `E'_r^{i,j} ≅ E_{r-1}^{-j,i+2j}`,
obtained from a specified isomorphism `E' ≅ renumber E`. -/
@[stacks 0G1Y "entry comparison for a renumbering", stacks 0G20]
noncomputable def entryIso {E : CohomologicalSpectralSequence C 1}
    {E' : E₂CohomologicalSpectralSequence C} (e : E' ≅ renumber E)
    (r : ℤ) (hr : 2 ≤ r) (i j : ℤ) :
    (E'.page r hr).X (i, j) ≅
      (E.page (r - 1) (one_le_priorPage r hr)).X (-j, i + 2 * j) :=
  (HomologicalComplex.eval C (newShape r) (i, j)).mapIso (pageIso e r hr)

/-- The entry comparison is the `(i,j)` component of the page comparison. -/
@[simp]
theorem entryIso_hom {E : CohomologicalSpectralSequence C 1}
    {E' : E₂CohomologicalSpectralSequence C} (e : E' ≅ renumber E)
    (r : ℤ) (hr : 2 ≤ r) (i j : ℤ) :
    (entryIso e r hr i j).hom = (pageIso e r hr).hom.f (i, j) := sorry

/-- The inverse entry comparison is the `(i,j)` component of the inverse page comparison. -/
@[simp]
theorem entryIso_inv {E : CohomologicalSpectralSequence C 1}
    {E' : E₂CohomologicalSpectralSequence C} (e : E' ≅ renumber E)
    (r : ℤ) (hr : 2 ≤ r) (i j : ℤ) :
    (entryIso e r hr i j).inv = (pageIso e r hr).inv.f (i, j) := sorry

/-- For the canonical renumbering itself, the entry comparison of the identity is the identity:
`(renumber E)_r^{i,j}` is literally `E_{r-1}^{-j,i+2j}`. -/
@[simp]
theorem entryIso_refl (E : CohomologicalSpectralSequence C 1) (r : ℤ) (hr : 2 ≤ r) (i j : ℤ) :
    entryIso (Iso.refl (renumber E)) r hr i j =
      Iso.refl ((E.page (r - 1) (one_le_priorPage r hr)).X (-j, i + 2 * j)) := sorry

end Renumber

namespace IsRenumbering

/-- Standard page-and-bidegree renumbering preserves boundedness. -/
@[stacks 0G1Y "boundedness under renumbering", stacks 0G20]
theorem isBounded_iff {E : CohomologicalSpectralSequence C 1}
    {E' : E₂CohomologicalSpectralSequence C} (h : IsRenumbering E E') :
    E'.IsBounded ↔ E.IsBounded := sorry

/-- A renumbering of a bounded spectral sequence is bounded. -/
@[stacks 0G1Y "bounded renumbering", stacks 0G20]
theorem isBounded {E : CohomologicalSpectralSequence C 1}
    {E' : E₂CohomologicalSpectralSequence C} (h : IsRenumbering E E')
    (hE : E.IsBounded) : E'.IsBounded := sorry

end IsRenumbering

end CohomologicalSpectralSequence
end CategoryTheory
