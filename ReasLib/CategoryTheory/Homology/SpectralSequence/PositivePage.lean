/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.SpectralSequence.Basic
public import Mathlib.Data.PNat.Basic

/-!
# Positive Pages of Spectral Sequences

This module packages the textbook positive-page indexing of a spectral sequence beginning at
`E₁`. It hides the lower-bound proof required by the underlying mathlib API and supplies the
corresponding page functor and page morphisms.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace SpectralSequence

variable {κ : Type*} {c : ℤ → ComplexShape κ}

namespace Page.One

/-- Reindex a spectral sequence beginning at page zero as the same spectral sequence beginning
at page one. This is independent of the shape of the individual pages. -/
@[stacks 0BDU "page-one reindexing"]
abbrev ofZero (E : SpectralSequence C c 0) : SpectralSequence C c 1 where
  page r _ := E.page r
  iso r r' pq hrr' _ := E.iso r r' pq

end Page.One

namespace Page.Zero

/-- The page family underlying `Page.Zero.ofOne`: the specified complex at zero and the supplied
spectral-sequence pages thereafter. -/
@[stacks 0BDU "zeroth-page extension page"]
noncomputable def ofOnePage
    (P : HomologicalComplex C (c 0)) (E : SpectralSequence C c 1)
    (r : ℤ) (hr : 0 ≤ r) : HomologicalComplex C (c r) :=
  if hzero : r = 0 then
    hzero ▸ P
  else
    E.page r (by omega)

/-- Adjoin a zeroth page to a spectral sequence beginning at page one.  The supplied
`pageOneIso` is exactly the transition from the homology of the new zeroth page to the first
page of the existing spectral sequence. -/
@[stacks 0BDU "zeroth-page extension"]
noncomputable def ofOne
    (P : HomologicalComplex C (c 0)) (E : SpectralSequence C c 1)
    (pageOneIso : ∀ pq : κ, P.homology pq ≅ (E.page 1).X pq) :
    SpectralSequence C c 0 where
  page r hr := ofOnePage P E r hr
  iso r r' pq hrr' hr := by
    by_cases hzero : r = 0
    · subst r
      subst r'
      simpa [ofOnePage] using pageOneIso pq
    · have hr' : 1 ≤ r := by omega
      have hr'zero : r' ≠ 0 := by omega
      simpa [ofOnePage, hzero, hr'zero] using E.iso r r' pq hrr' hr'

/-- The zeroth page of `Page.Zero.ofOne` is the specified initial complex. -/
@[simp, stacks 0BDU "zeroth-page extension at zero"]
theorem ofOne_page_zero
    (P : HomologicalComplex C (c 0)) (E : SpectralSequence C c 1)
    (pageOneIso : ∀ pq : κ, P.homology pq ≅ (E.page 1).X pq) :
    (ofOne P E pageOneIso).page 0 = P := sorry

/-- Every positive page of `Page.Zero.ofOne` agrees with the input page-one spectral sequence. -/
@[simp, stacks 0BDU "zeroth-page extension at positive pages"]
theorem ofOne_page_pos
    (P : HomologicalComplex C (c 0)) (E : SpectralSequence C c 1)
    (pageOneIso : ∀ pq : κ, P.homology pq ≅ (E.page 1).X pq)
    (r : ℤ) (hr : 1 ≤ r) :
    (ofOne P E pageOneIso).page r (zero_le_one.trans hr) = E.page r hr := sorry

/-- The transition from page zero to page one in `Page.Zero.ofOne` is the supplied
identification. -/
@[simp, stacks 0BDU "zeroth-page extension transition"]
theorem ofOne_iso_zero
    (P : HomologicalComplex C (c 0)) (E : SpectralSequence C c 1)
    (pageOneIso : ∀ pq : κ, P.homology pq ≅ (E.page 1).X pq) (pq : κ) :
    (ofOne P E pageOneIso).iso 0 1 pq = pageOneIso pq := sorry

end Page.Zero

/-- The `n`-th zero-based page, so `pageComplex E n` is the textbook page `E_{n + 1}`. -/
abbrev pageComplex (E : SpectralSequence C c 1) (n : ℕ) :
    HomologicalComplex C (c (Nat.succ n : ℤ)) :=
  E.page (Nat.succ n : ℤ)

/-- The textbook page `E_r` for a positive page index `r`. -/
@[stacks 011O "positive-page indexing"]
abbrev positivePage (E : SpectralSequence C c 1) (r : ℕ+) :
    HomologicalComplex C (c (r : ℤ)) :=
  E.page (r : ℤ) (Int.ofNat_le.mpr (Nat.succ_le_iff.mpr r.pos))

namespace Hom

/-- The morphism on the textbook positive page `E_r`. -/
abbrev positivePage {E E' : SpectralSequence C c 1}
    (f : E ⟶ E') (r : ℕ+) : E.positivePage r ⟶ E'.positivePage r :=
  f.hom (r : ℤ) (Int.ofNat_le.mpr (Nat.succ_le_iff.mpr r.pos))

end Hom

/-- Evaluation at the textbook positive page `E_r`. -/
@[stacks 011O "positive-page evaluation functor"]
def positivePageFunctor (c : ℤ → ComplexShape κ) (r : ℕ+) :
    SpectralSequence C c 1 ⥤ HomologicalComplex C (c (r : ℤ)) :=
  pageFunctor C c 1 (r : ℤ) (Int.ofNat_le.mpr (Nat.succ_le_iff.mpr r.pos))

namespace PositivePageFunctor

/-- Evaluation of `positivePageFunctor` on a spectral sequence is its textbook page `E_r`. -/
@[simp]
theorem obj (c : ℤ → ComplexShape κ) (r : ℕ+)
    (E : SpectralSequence C c 1) :
    (positivePageFunctor c r).obj E = E.positivePage r := sorry

/-- Evaluation of `positivePageFunctor` on a morphism is its positive-page component. -/
@[simp]
theorem map (c : ℤ → ComplexShape κ) (r : ℕ+)
    {E E' : SpectralSequence C c 1} (f : E ⟶ E') :
    (positivePageFunctor c r).map f = f.positivePage r := sorry

end PositivePageFunctor

/-- The entry `E_r^{pq}` on a positive page. -/
@[stacks 011O "positive-page entry"]
abbrev pageObject (E : SpectralSequence C c 1) (pq : κ) (r : ℕ+) : C :=
  (E.positivePage r).X pq

namespace PositivePage

/-- The homology at `pq` of a positive page is canonically the corresponding entry of its next
positive page. -/
@[stacks 011O "positive-page homology transition"]
noncomputable def homologyIso (E : SpectralSequence C c 1) (pq : κ) (r : ℕ+) :
    (E.positivePage r).homology pq ≅ E.pageObject pq (r + 1) :=
  E.iso (r : ℤ) ((r + 1 : ℕ+) : ℤ) pq
    (Eq.symm
      (Eq.trans
        (congrArg (fun n : ℕ => (n : ℤ)) (PNat.add_coe r 1))
        (Int.natCast_add (r : ℕ) 1)))
    (Int.ofNat_le.mpr (Nat.succ_le_iff.mpr r.pos))

/-- The positive-page homology comparison is natural in a spectral-sequence morphism. -/
@[reassoc, stacks 011O "naturality of the positive-page homology comparison"]
theorem homologyIso_hom_naturality
    {E E' : SpectralSequence C c 1} (f : E ⟶ E') (pq : κ) (r : ℕ+) :
    HomologicalComplex.homologyMap (f.positivePage r) pq ≫
        (homologyIso E' pq r).hom =
      (homologyIso E pq r).hom ≫ (f.positivePage (r + 1)).f pq := sorry

/-- The inverse positive-page homology comparison is natural in a spectral-sequence morphism. -/
@[reassoc, stacks 011O "inverse naturality of the positive-page homology comparison"]
theorem homologyIso_inv_naturality
    {E E' : SpectralSequence C c 1} (f : E ⟶ E') (pq : κ) (r : ℕ+) :
    (f.positivePage (r + 1)).f pq ≫ (homologyIso E' pq r).inv =
      (homologyIso E pq r).inv ≫
        HomologicalComplex.homologyMap (f.positivePage r) pq := sorry

end PositivePage

/-- Evaluation at the entry `E_r^{pq}` of a positive page. -/
@[stacks 011O "positive-page entry functor"]
noncomputable def pageObjectFunctor (c : ℤ → ComplexShape κ) (r : ℕ+) (pq : κ) :
    SpectralSequence C c 1 ⥤ C :=
  positivePageFunctor c r ⋙ HomologicalComplex.eval C (c (r : ℤ)) pq

namespace PageObjectFunctor

/-- Evaluation of the positive-page entry functor on a spectral sequence is the corresponding
page entry. -/
@[simp]
theorem obj (c : ℤ → ComplexShape κ) (r : ℕ+) (pq : κ)
    (E : SpectralSequence C c 1) :
    (pageObjectFunctor c r pq).obj E = E.pageObject pq r := sorry

/-- Evaluation of the positive-page entry functor on a spectral-sequence morphism is its
corresponding entry map. -/
@[simp]
theorem map (c : ℤ → ComplexShape κ) (r : ℕ+) (pq : κ)
    {E E' : SpectralSequence C c 1} (f : E ⟶ E') :
    (pageObjectFunctor c r pq).map f = (f.positivePage r).f pq := sorry

end PageObjectFunctor

/-- Textbook notation for the page entry `E_r^{pq}`. -/
scoped notation:max E "⟦" r "," pq "⟧" => SpectralSequence.pageObject E pq r

end SpectralSequence

end CategoryTheory
