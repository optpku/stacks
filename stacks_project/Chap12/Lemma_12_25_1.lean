/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Homology.DoubleComplex.Pages
public import ReasLib.CategoryTheory.Homology.DoubleComplex.Filtration.InitialPages.First
public import ReasLib.CategoryTheory.Homology.DoubleComplex.Filtration.InitialPages.Second
import StacksCheckRecall

/-!
# Lemma 12.25.1

Source-facing checks for the initial pages of the two spectral sequences associated to a
cohomological double complex.  The reusable constructions are owned by
`HomologicalComplex₂` in `ReasLib`.
-/

@[expose] public section

open CategoryTheory ComplexShape

noncomputable section

universe v u

namespace CategoryTheory

section RawPages

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {K : HomologicalComplex₂ C (up ℤ) (up ℤ)} (p q : ℤ)

/- Lemma 12.25.1 (1): the first page-zero entry is `K^{p,q}`. -/
@[stacks 0130]
#check (HomologicalComplex₂.First.PageZero.entry K p q : C)

/- Lemma 12.25.1 (2): its differential is the signed vertical differential. -/
@[stacks 0130]
#check (HomologicalComplex₂.First.PageZero.differential K p q :
  HomologicalComplex₂.First.PageZero.entry K p q ⟶
    HomologicalComplex₂.First.PageZero.entry K p (q + 1))

/- Lemma 12.25.1 (3): the second page-zero entry is the transposed entry `K^{q,p}`. -/
@[stacks 0130]
#check (HomologicalComplex₂.Second.PageZero.entry K p q : C)

/- Lemma 12.25.1 (4): its differential is the horizontal differential of `K`. -/
@[stacks 0130]
#check (HomologicalComplex₂.Second.PageZero.differential K p q :
  HomologicalComplex₂.Second.PageZero.entry K p q ⟶
    HomologicalComplex₂.Second.PageZero.entry K p (q + 1))

section Homology

variable [CategoryWithHomology C]

/- Lemma 12.25.1 (5): the first page-one entries are vertical homology. -/
@[stacks 0130]
#check (HomologicalComplex₂.First.PageOne.entry K p q : C)

/- Lemma 12.25.1 (6): the first page-one differential is induced horizontally. -/
@[stacks 0130]
#check (HomologicalComplex₂.First.PageOne.differential K p q :
  HomologicalComplex₂.First.PageOne.entry K p q ⟶
    HomologicalComplex₂.First.PageOne.entry K (p + 1) q)

/- Lemma 12.25.1 (7): the second page-one entries are horizontal homology. -/
@[stacks 0130]
#check (HomologicalComplex₂.Second.PageOne.entry K p q : C)

/- Lemma 12.25.1 (8): the second page-one differential carries the standard sign. -/
@[stacks 0130]
#check (HomologicalComplex₂.Second.PageOne.differential K p q :
  HomologicalComplex₂.Second.PageOne.entry K p q ⟶
    HomologicalComplex₂.Second.PageOne.entry K (p + 1) q)

/- Lemma 12.25.1 (9): the first page-two entries are the homology of the first page-one
complex. -/
@[stacks 0130]
#check (HomologicalComplex₂.First.PageTwo.entry K p q : C)

/- Lemma 12.25.1 (10): the second page-two entries are the homology of the second page-one
complex. -/
@[stacks 0130]
#check (HomologicalComplex₂.Second.PageTwo.entry K p q : C)

end Homology

end RawPages

section AssociatedPages

open HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {K : HomologicalComplex₂ C (up ℤ) (up ℤ)} [K.HasTotal (up ℤ)]
variable {E₁ E₂ : CohomologicalSpectralSequence C 0}
variable (A₁ : FilteredComplex.Association (First.Filtration.total K) E₁)
variable (A₂ : FilteredComplex.Association (Second.Filtration.total K) E₂) (p q : ℤ)

/- The actual zeroth-page columns have the signed vertical and unsigned horizontal
differentials, respectively. The comparison laws follow from the ambient hypotheses. -/
@[stacks 0130]
#check (A₁.columnIso p ≪≫ First.GradedPiece.columnIsoOf K p
  (First.GradedPiece.comparisons K p) :
  E₁.pageZeroColumn p ≅ CochainComplex.rescaleDifferential (K.X p) (p.negOnePow : ℤ))

@[stacks 0130]
#check (A₂.columnIso p ≪≫ Second.GradedPiece.rowIsoOf K p
  (Second.GradedPiece.comparisons K p) : E₂.pageZeroColumn p ≅ K.flip.X p)

/- The comparisons identify the entries of the associated sequences themselves. -/
@[stacks 0130]
#check ((CohomologicalSpectralSequence.PageZeroColumn.xIso E₁ p q).symm ≪≫
  HomologicalComplex.Hom.isoApp (A₁.columnIso p ≪≫ First.GradedPiece.columnIsoOf K p
    (First.GradedPiece.comparisons K p)) q :
  (E₁.page 0).X (p, q) ≅ First.PageZero.entry K p q)

@[stacks 0130]
#check ((CohomologicalSpectralSequence.PageZeroColumn.xIso E₂ p q).symm ≪≫
  HomologicalComplex.Hom.isoApp (A₂.columnIso p ≪≫ Second.GradedPiece.rowIsoOf K p
    (Second.GradedPiece.comparisons K p)) q :
  (E₂.page 0).X (p, q) ≅ Second.PageZero.entry K p q)

@[stacks 0130]
#check (First.Association.pageOneIso A₁ (First.GradedPiece.comparisons K) p q :
  (E₁.page 1).X (p, q) ≅ First.PageOne.entry K p q)

@[stacks 0130]
#check (Second.Association.pageOneIso A₂ (Second.GradedPiece.comparisons K) p q :
  (E₂.page 1).X (p, q) ≅ Second.PageOne.entry K p q)

/- The first-page differentials are the induced horizontal map and the signed induced
vertical map from the source formulas. -/
@[stacks 0130]
#check (First.Association.pageOneIso_commSq A₁ (First.GradedPiece.comparisons K) p q :
  CommSq ((E₁.page 1).d (p, q) (p + 1, q))
    (First.Association.pageOneIso A₁ (First.GradedPiece.comparisons K) p q).hom
    (First.Association.pageOneIso A₁ (First.GradedPiece.comparisons K) (p + 1) q).hom
    (First.PageOne.differential K p q))

@[stacks 0130]
#check (Second.Association.pageOneIso_commSq A₂ (Second.GradedPiece.comparisons K) p q :
  CommSq ((E₂.page 1).d (p, q) (p + 1, q))
    (Second.Association.pageOneIso A₂ (Second.GradedPiece.comparisons K) p q).hom
    (Second.Association.pageOneIso A₂ (Second.GradedPiece.comparisons K) (p + 1) q).hom
    (Second.PageOne.differential K p q))

@[stacks 0130]
#check (First.Association.pageTwoIso A₁ (First.GradedPiece.comparisons K) p q :
  (E₁.page 2).X (p, q) ≅ First.PageTwo.entry K p q)

@[stacks 0130]
#check (Second.Association.pageTwoIso A₂ (Second.GradedPiece.comparisons K) p q :
  (E₂.page 2).X (p, q) ≅ Second.PageTwo.entry K p q)

end AssociatedPages

end CategoryTheory
