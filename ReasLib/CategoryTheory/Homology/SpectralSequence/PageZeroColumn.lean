/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.Embedding.RestrictionHomology
public import Mathlib.Algebra.Homology.SpectralSequence.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Fixed Columns of the Zeroth Page of a Cohomological Spectral Sequence

The zeroth differential of a cohomological spectral sequence preserves the first bidegree.
This file packages a fixed column as an ordinary cochain complex. The embedding, object
comparisons, maps, and homology comparison are independent of any realization of the spectral
sequence, so they belong to the spectral-sequence owner rather than to filtered complexes.
-/

@[expose] public section

open CategoryTheory ComplexShape

noncomputable section

universe u v

namespace CategoryTheory
namespace CohomologicalSpectralSequence

/-- The complex shape of the zeroth page, kept in the unreduced form used by
`CohomologicalSpectralSequence.page`. -/
abbrev pageZeroShape : ComplexShape (ℤ × ℤ) :=
  up' (⟨(0 : ℤ), 1 - 0⟩ : ℤ × ℤ)

namespace PageZeroColumn

/-- The inclusion of a fixed column into the bidegree shape of the zeroth page is injective. -/
theorem index_injective (p : ℤ) :
    Function.Injective (fun q : ℤ ↦ (p, q)) := sorry

/-- Fixing the first coordinate identifies the ordinary cochain relation with the relation on
the zeroth page of a cohomological spectral sequence. -/
theorem rel_iff (p i j : ℤ) :
    (up ℤ).Rel i j ↔
      pageZeroShape.Rel (p, i) (p, j) := sorry

/-- The complex-shape embedding which includes the column with first coordinate `p` into a
cohomological page-zero shape. -/
def embedding (p : ℤ) :
    (up ℤ).Embedding pageZeroShape :=
  ComplexShape.Embedding.mk' (up ℤ) pageZeroShape
    (fun q ↦ (p, q)) (index_injective p) (rel_iff p)

/-- The fixed-column embedding preserves and reflects the complex-shape relation. -/
instance embedding_isRelIff (p : ℤ) :
    (embedding p).IsRelIff := sorry

/-- Evaluation of the page-zero column embedding. -/
@[simp]
theorem embedding_f (p q : ℤ) :
    (embedding p).f q = (p, q) := sorry

/-- The predecessor of `(p,q)` in the page-zero shape lies in the same column. -/
theorem page_prev (p q : ℤ) :
    pageZeroShape.prev (p, q) = (p, q - 1) := sorry

/-- The successor of `(p,q)` in the page-zero shape lies in the same column. -/
theorem page_next (p q : ℤ) :
    pageZeroShape.next (p, q) = (p, q + 1) := sorry

end PageZeroColumn

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The column of the zeroth page of a cohomological spectral sequence with fixed first
coordinate, presented as an ordinary `ℤ`-indexed cochain complex. -/
@[stacks 012M "a fixed column of the zeroth page"]
abbrev pageZeroColumn (E : CohomologicalSpectralSequence C 0) (p : ℤ) :
    CochainComplex C ℤ :=
  (E.page 0).restriction (PageZeroColumn.embedding p)

namespace PageZeroColumn

/-- The object of a restricted page-zero column is canonically the corresponding page entry. -/
@[stacks 012M "object comparison for a fixed zeroth-page column"]
noncomputable def xIso
    (E : CohomologicalSpectralSequence C 0) (p q : ℤ) :
    (E.pageZeroColumn p).X q ≅ (E.page 0).X (p, q) :=
  (E.page 0).restrictionXIso (embedding p) (embedding_f p q)

/-- Equality form of the object comparison for a fixed page-zero column. -/
theorem obj_eq (E : CohomologicalSpectralSequence C 0) (p q : ℤ) :
    (E.pageZeroColumn p).X q = (E.page 0).X (p, q) := sorry

/-- The object comparisons identify the restricted differential with the vertical page
differential. -/
@[reassoc]
theorem xIso_hom_d
    (E : CohomologicalSpectralSequence C 0) (p q : ℤ) :
    (xIso E p q).hom ≫ (E.page 0).d (p, q) (p, q + 1) =
      (E.pageZeroColumn p).d q (q + 1) ≫ (xIso E p (q + 1)).hom := sorry

/-- Restriction of a spectral-sequence morphism to a fixed column of the zeroth page. -/
noncomputable def map {E E' : CohomologicalSpectralSequence C 0}
    (f : E ⟶ E') (p : ℤ) : E.pageZeroColumn p ⟶ E'.pageZeroColumn p :=
  HomologicalComplex.restrictionMap (f.hom 0) (embedding p)

/-- A restricted page-zero map is evaluated componentwise on the original page map. -/
@[simp]
theorem map_f {E E' : CohomologicalSpectralSequence C 0}
    (f : E ⟶ E') (p q : ℤ) :
    (map f p).f q = (f.hom 0).f (p, q) := sorry

/-- Restricting the identity spectral-sequence morphism gives the identity column map. -/
@[simp]
theorem map_id (E : CohomologicalSpectralSequence C 0) (p : ℤ) :
    map (𝟙 E) p = 𝟙 (E.pageZeroColumn p) := sorry

/-- Restriction to a page-zero column preserves composition. -/
@[simp]
theorem map_comp {E E' E'' : CohomologicalSpectralSequence C 0}
    (f : E ⟶ E') (g : E' ⟶ E'') (p : ℤ) :
    map (f ≫ g) p = map f p ≫ map g p := sorry

/-- The column object comparisons are natural for morphisms of spectral sequences. -/
@[reassoc, stacks 012M "naturality of fixed-column object comparisons"]
theorem xIso_hom_naturality
    {E E' : CohomologicalSpectralSequence C 0} (f : E ⟶ E') (p q : ℤ) :
    (map f p).f q ≫ (xIso E' p q).hom =
      (xIso E p q).hom ≫ (f.hom 0).f (p, q) := sorry

/-- The inverse column object comparisons are natural for morphisms of spectral sequences. -/
@[reassoc, stacks 012M "inverse naturality of fixed-column object comparisons"]
theorem xIso_inv_naturality
    {E E' : CohomologicalSpectralSequence C 0} (f : E ⟶ E') (p q : ℤ) :
    (f.hom 0).f (p, q) ≫ (xIso E' p q).inv =
      (xIso E p q).inv ≫ (map f p).f q := sorry

/-- Fixing the first coordinate makes the zeroth-page column construction functorial. -/
noncomputable def functor (p : ℤ) :
    CohomologicalSpectralSequence C 0 ⥤ CochainComplex C ℤ where
  obj E := E.pageZeroColumn p
  map f := map f p
  map_id E := map_id E p
  map_comp f g := map_comp f g p

namespace Functor

/-- The fixed-column functor evaluates a spectral sequence at its restricted zeroth-page column. -/
@[simp]
theorem obj (E : CohomologicalSpectralSequence C 0) (p : ℤ) :
    (functor (C := C) p).obj E = E.pageZeroColumn p := sorry

/-- The fixed-column functor evaluates a spectral-sequence morphism by restriction to that column. -/
@[simp]
theorem map {E E' : CohomologicalSpectralSequence C 0}
    (f : E ⟶ E') (p : ℤ) :
    (functor (C := C) p).map f = PageZeroColumn.map f p := sorry

end Functor

/-- Homology of a restricted page-zero column agrees with homology of the full page at the
corresponding bidegree. -/
@[stacks 012M "homology of a fixed column of the zeroth page"]
noncomputable def homologyIso
    (E : CohomologicalSpectralSequence C 0) (p q : ℤ) :
    (E.pageZeroColumn p).homology q ≅ (E.page 0).homology (p, q) :=
  (E.page 0).restrictionHomologyIso (embedding p)
    (q - 1) q (q + 1) (CochainComplex.prev ℤ q) (CochainComplex.next ℤ q)
    (embedding_f p (q - 1)) (embedding_f p q)
      (embedding_f p (q + 1))
    (page_prev p q) (page_next p q)

/-- The fixed-column homology comparison is natural in morphisms of spectral sequences. -/
theorem homologyIso_hom_naturality
    {E E' : CohomologicalSpectralSequence C 0} (f : E ⟶ E') (p q : ℤ) :
    HomologicalComplex.homologyMap (map f p) q ≫
        (homologyIso E' p q).hom =
      (homologyIso E p q).hom ≫
        HomologicalComplex.homologyMap (f.hom 0) (p, q) := sorry

/-- The inverse fixed-column homology comparison is natural in morphisms of spectral sequences. -/
@[reassoc, stacks 012M "inverse naturality of the fixed-column homology comparison"]
theorem homologyIso_inv_naturality
    {E E' : CohomologicalSpectralSequence C 0} (f : E ⟶ E') (p q : ℤ) :
    HomologicalComplex.homologyMap (f.hom 0) (p, q) ≫
        (homologyIso E' p q).inv =
      (homologyIso E p q).inv ≫
        HomologicalComplex.homologyMap (map f p) q := sorry

end PageZeroColumn

end CohomologicalSpectralSequence
end CategoryTheory
