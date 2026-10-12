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
# Fixed Rows of the First Page of a Cohomological Spectral Sequence

The first differential of a cohomological spectral sequence preserves the second bidegree.
This file packages a fixed row as an ordinary cochain complex.  The embedding, its relation
instance, object comparisons, maps, and homology comparison are exposed independently so that
clients do not need to unfold restriction along a complex-shape embedding.
-/

@[expose] public section

open CategoryTheory ComplexShape

noncomputable section

universe u v

namespace CategoryTheory
namespace CohomologicalSpectralSequence

/-- The complex shape of the first page, kept in the unreduced form used by
`CohomologicalSpectralSequence.page`. -/
abbrev pageOneShape : ComplexShape (ℤ × ℤ) :=
  up' (⟨(1 : ℤ), 1 - 1⟩ : ℤ × ℤ)

namespace PageOneRow

/-- The inclusion of a fixed row into the bidegree shape of the first page is injective. -/
theorem index_injective (q : ℤ) :
    Function.Injective (fun p : ℤ ↦ (p, q)) := sorry

/-- Fixing the second coordinate identifies the ordinary cochain relation with the relation on
the first page of a cohomological spectral sequence. -/
theorem rel_iff (q i j : ℤ) :
    (up ℤ).Rel i j ↔
      pageOneShape.Rel (i, q) (j, q) := sorry

/-- The complex-shape embedding which includes the row with second coordinate `q` into a
cohomological page-one shape. -/
def embedding (q : ℤ) :
    (up ℤ).Embedding pageOneShape :=
  ComplexShape.Embedding.mk' (up ℤ) pageOneShape
    (fun p ↦ (p, q)) (index_injective q) (rel_iff q)

/-- The fixed-row embedding preserves and reflects the complex-shape relation. -/
instance embedding_isRelIff (q : ℤ) :
    (embedding q).IsRelIff := sorry

/-- Evaluation of the page-one row embedding. -/
@[simp]
theorem embedding_f (q p : ℤ) :
    (embedding q).f p = (p, q) := sorry

/-- The predecessor of `(p,q)` in the page-one shape lies in the same row. -/
theorem page_prev (p q : ℤ) :
    pageOneShape.prev (p, q) = (p - 1, q) := sorry

/-- The successor of `(p,q)` in the page-one shape lies in the same row. -/
theorem page_next (p q : ℤ) :
    pageOneShape.next (p, q) = (p + 1, q) := sorry

end PageOneRow

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The row of the first page of a cohomological spectral sequence with fixed second coordinate,
presented as an ordinary `ℤ`-indexed cochain complex. -/
@[stacks 0130 "a fixed row of the first page"]
abbrev pageOneRow (E : CohomologicalSpectralSequence C 0) (q : ℤ) :
    CochainComplex C ℤ :=
  (E.page 1).restriction (PageOneRow.embedding q)

namespace PageOneRow

/-- The object of a restricted page-one row is canonically the corresponding page entry. -/
@[stacks 0130 "object comparison for a fixed row"]
noncomputable def xIso
    (E : CohomologicalSpectralSequence C 0) (p q : ℤ) :
    (E.pageOneRow q).X p ≅ (E.page 1).X (p, q) :=
  (E.page 1).restrictionXIso (embedding q) (embedding_f q p)

/-- Equality form of the object comparison for a restricted page-one row. -/
theorem obj_eq (E : CohomologicalSpectralSequence C 0) (p q : ℤ) :
    (E.pageOneRow q).X p = (E.page 1).X (p, q) := sorry

/-- The object comparisons identify the restricted differential with the horizontal page
differential. -/
@[reassoc]
theorem xIso_hom_d
    (E : CohomologicalSpectralSequence C 0) (p q : ℤ) :
    (xIso E p q).hom ≫ (E.page 1).d (p, q) (p + 1, q) =
      (E.pageOneRow q).d p (p + 1) ≫ (xIso E (p + 1) q).hom := sorry

/-- Restriction of a spectral-sequence morphism to a fixed row of the first page. -/
noncomputable def map {E E' : CohomologicalSpectralSequence C 0}
    (f : E ⟶ E') (q : ℤ) : E.pageOneRow q ⟶ E'.pageOneRow q :=
  HomologicalComplex.restrictionMap (f.hom 1) (embedding q)

/-- A restricted page-one map is evaluated componentwise on the original page map. -/
@[simp]
theorem map_f {E E' : CohomologicalSpectralSequence C 0}
    (f : E ⟶ E') (p q : ℤ) :
    (map f q).f p = (f.hom 1).f (p, q) := sorry

/-- Restricting the identity spectral-sequence morphism gives the identity row map. -/
@[simp]
theorem map_id (E : CohomologicalSpectralSequence C 0) (q : ℤ) :
    map (𝟙 E) q = 𝟙 (E.pageOneRow q) := sorry

/-- Restriction to a page-one row preserves composition. -/
@[simp]
theorem map_comp {E E' E'' : CohomologicalSpectralSequence C 0}
    (f : E ⟶ E') (g : E' ⟶ E'') (q : ℤ) :
    map (f ≫ g) q = map f q ≫ map g q := sorry

/-- The row object comparisons are natural for morphisms of spectral sequences. -/
@[reassoc, stacks 0130 "naturality of fixed-row object comparisons"]
theorem xIso_hom_naturality
    {E E' : CohomologicalSpectralSequence C 0} (f : E ⟶ E') (p q : ℤ) :
    (map f q).f p ≫ (xIso E' p q).hom =
      (xIso E p q).hom ≫ (f.hom 1).f (p, q) := sorry

/-- The inverse row object comparisons are natural for morphisms of spectral sequences. -/
@[reassoc, stacks 0130 "inverse naturality of fixed-row object comparisons"]
theorem xIso_inv_naturality
    {E E' : CohomologicalSpectralSequence C 0} (f : E ⟶ E') (p q : ℤ) :
    (f.hom 1).f (p, q) ≫ (xIso E' p q).inv =
      (xIso E p q).inv ≫ (map f q).f p := sorry

/-- Fixing the second coordinate makes the first-page row construction functorial. -/
@[stacks 0130 "fixed-row functor on the first spectral-sequence page"]
noncomputable def functor (q : ℤ) :
    CohomologicalSpectralSequence C 0 ⥤ CochainComplex C ℤ where
  obj E := E.pageOneRow q
  map f := map f q
  map_id E := map_id E q
  map_comp f g := map_comp f g q

namespace Functor

/-- The fixed-row functor evaluates a spectral sequence at its restricted first-page row. -/
@[simp]
theorem obj (E : CohomologicalSpectralSequence C 0) (q : ℤ) :
    (functor (C := C) q).obj E = E.pageOneRow q := sorry

/-- The fixed-row functor evaluates a spectral-sequence morphism by restriction to that row. -/
@[simp]
theorem map {E E' : CohomologicalSpectralSequence C 0}
    (f : E ⟶ E') (q : ℤ) :
    (functor (C := C) q).map f = PageOneRow.map f q := sorry

end Functor

/-- Homology of a restricted page-one row agrees with homology of the full page at the
corresponding bidegree. -/
@[stacks 0130 "homology of a fixed row of the first page"]
noncomputable def homologyIso
    (E : CohomologicalSpectralSequence C 0) (p q : ℤ) :
    (E.pageOneRow q).homology p ≅ (E.page 1).homology (p, q) :=
  (E.page 1).restrictionHomologyIso (embedding q)
    (p - 1) p (p + 1) (CochainComplex.prev ℤ p) (CochainComplex.next ℤ p)
    (embedding_f q (p - 1)) (embedding_f q p)
      (embedding_f q (p + 1))
    (page_prev p q) (page_next p q)

/-- The fixed-row homology comparison is natural in morphisms of spectral sequences. -/
@[reassoc]
theorem homologyIso_hom_naturality
    {E E' : CohomologicalSpectralSequence C 0} (f : E ⟶ E') (p q : ℤ) :
    HomologicalComplex.homologyMap (map f q) p ≫
        (homologyIso E' p q).hom =
      (homologyIso E p q).hom ≫
        HomologicalComplex.homologyMap (f.hom 1) (p, q) := sorry

/-- The inverse fixed-row homology comparison is natural in morphisms of spectral sequences. -/
@[reassoc, stacks 0130 "inverse naturality of the fixed-row homology comparison"]
theorem homologyIso_inv_naturality
    {E E' : CohomologicalSpectralSequence C 0} (f : E ⟶ E') (p q : ℤ) :
    HomologicalComplex.homologyMap (f.hom 1) (p, q) ≫
        (homologyIso E' p q).inv =
      (homologyIso E p q).inv ≫
        HomologicalComplex.homologyMap (map f q) p := sorry

/-- An isomorphism from a fixed first-page row to a cochain complex induces the corresponding
second-page comparison. -/
@[stacks 0130 "second page from a fixed-row comparison"]
noncomputable def pageTwoIso
    {E : CohomologicalSpectralSequence C 0} {q : ℤ} {R : CochainComplex C ℤ}
    (e : E.pageOneRow q ≅ R) (p : ℤ) :
    (E.page 2).X (p, q) ≅ R.homology p :=
  (E.iso 1 2 (p, q)).symm ≪≫
    (homologyIso E p q).symm ≪≫
      HomologicalComplex.homologyMapIso e p

/-- The forward fixed-row second-page comparison is induced by the supplied row isomorphism. -/
@[simp]
theorem pageTwoIso_hom
    {E : CohomologicalSpectralSequence C 0} {q : ℤ} {R : CochainComplex C ℤ}
    (e : E.pageOneRow q ≅ R) (p : ℤ) :
    (pageTwoIso e p).hom =
      (E.iso 1 2 (p, q)).inv ≫
        (homologyIso E p q).inv ≫
          HomologicalComplex.homologyMap e.hom p := sorry

/-- The inverse fixed-row second-page comparison is induced by the inverse row isomorphism. -/
@[simp]
theorem pageTwoIso_inv
    {E : CohomologicalSpectralSequence C 0} {q : ℤ} {R : CochainComplex C ℤ}
    (e : E.pageOneRow q ≅ R) (p : ℤ) :
    (pageTwoIso e p).inv =
      HomologicalComplex.homologyMap e.inv p ≫
        (homologyIso E p q).hom ≫
          (E.iso 1 2 (p, q)).hom := sorry

/-- A presentation of one fixed row of the first page of a cohomological spectral sequence.  The
presentation identifies its entries with a chosen cochain complex and records compatibility with
the first differential. -/
@[stacks 0130 "rowwise presentation of the first spectral-sequence page"]
structure Presentation
    (E : CohomologicalSpectralSequence C 0) (q : ℤ) (R : CochainComplex C ℤ) where
  /-- The comparison from a first-page entry to the chosen row complex. -/
  entryIso : ∀ p : ℤ, (E.page 1).X (p, q) ≅ R.X p
  /-- The entry comparisons intertwine the first-page differential and the row differential. -/
  comm : ∀ p : ℤ,
    CommSq
      ((E.page 1).d (p, q) (p + 1, q))
      (entryIso p).hom
      (entryIso (p + 1)).hom
      (R.d p (p + 1))

namespace Presentation

variable {E : CohomologicalSpectralSequence C 0} {q : ℤ} {R : CochainComplex C ℤ}

/-- The componentwise comparison from a restricted row of `E₁` to the presented row complex. -/
noncomputable def rowIso (P : Presentation E q R) (p : ℤ) :
    (E.pageOneRow q).X p ≅ R.X p :=
  xIso E p q ≪≫ P.entryIso p

/-- The forward row comparison is the restriction comparison followed by the presentation. -/
@[simp]
theorem rowIso_hom (P : Presentation E q R) (p : ℤ) :
    (P.rowIso p).hom = (xIso E p q).hom ≫ (P.entryIso p).hom := sorry

/-- The inverse row comparison first inverts the presentation and then the restriction map. -/
@[simp]
theorem rowIso_inv (P : Presentation E q R) (p : ℤ) :
    (P.rowIso p).inv = (P.entryIso p).inv ≫ (xIso E p q).inv := sorry

/-- The row comparisons commute with every differential of the restricted first-page row. -/
theorem rowIso_comm (P : Presentation E q R) (i j : ℤ) (hij : (up ℤ).Rel i j) :
    (P.rowIso i).hom ≫ R.d i j =
      (E.pageOneRow q).d i j ≫ (P.rowIso j).hom := sorry

/-- A rowwise presentation assembles into an isomorphism of cochain complexes. -/
noncomputable def complexIso (P : Presentation E q R) :
    E.pageOneRow q ≅ R :=
  HomologicalComplex.Hom.isoOfComponents
    P.rowIso
    P.rowIso_comm

/-- The forward row-complex isomorphism evaluates to the componentwise row comparison. -/
@[simp]
theorem complexIso_hom_f (P : Presentation E q R) (p : ℤ) :
    P.complexIso.hom.f p = (P.rowIso p).hom := sorry

/-- The inverse row-complex isomorphism evaluates to the inverse row comparison. -/
@[simp]
theorem complexIso_inv_f (P : Presentation E q R) (p : ℤ) :
    P.complexIso.inv.f p = (P.rowIso p).inv := sorry

/-- A rowwise presentation identifies the second page with homology of the presented row. -/
noncomputable def pageTwoIso (P : Presentation E q R) (p : ℤ) :
    (E.page 2).X (p, q) ≅ R.homology p :=
  PageOneRow.pageTwoIso P.complexIso p

/-- The forward second-page comparison is induced by the presented row-complex isomorphism. -/
@[simp]
theorem pageTwoIso_hom (P : Presentation E q R) (p : ℤ) :
    (P.pageTwoIso p).hom =
      (E.iso 1 2 (p, q)).inv ≫
        (homologyIso E p q).inv ≫
        HomologicalComplex.homologyMap P.complexIso.hom p := sorry

/-- The inverse second-page comparison is induced by the inverse presented row-complex
isomorphism. -/
@[simp]
theorem pageTwoIso_inv (P : Presentation E q R) (p : ℤ) :
    (P.pageTwoIso p).inv =
      HomologicalComplex.homologyMap P.complexIso.inv p ≫
        (homologyIso E p q).hom ≫
        (E.iso 1 2 (p, q)).hom := sorry

end Presentation

end PageOneRow

end CohomologicalSpectralSequence
end CategoryTheory
