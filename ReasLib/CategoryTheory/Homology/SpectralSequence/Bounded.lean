module

public import Mathlib.Data.Int.ConditionallyCompleteOrder
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Homology.SpectralSequence.PageFiltration

/-!
# Bounded Cohomological Spectral Sequences

@stack 0BDU
@stack 0BDV

This file contains regularity, coregularity, and boundedness conditions for a cohomological
spectral sequence.  These conditions depend only on the spectral sequence itself.  The cycle and
boundary stabilization criteria use the page-filtration owner after reindexing an arbitrary
initial page as page one.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v

namespace CategoryTheory
namespace CohomologicalSpectralSequence

variable {C : Type u} [Category.{v} C] [Abelian C] {r₀ : ℤ}

namespace Page
namespace One

/-- Forgetting the zeroth page views a cohomological spectral sequence starting at zero as the
same spectral sequence starting at page one. -/
@[stacks 0BDU "page-one presentation"]
abbrev ofZero (E : CohomologicalSpectralSequence C 0) :
    SpectralSequence C (fun r ↦ ComplexShape.up' (⟨r, 1 - r⟩ : ℤ × ℤ)) 1 :=
  SpectralSequence.Page.One.ofZero E

/-- Reindexing a page `r ≥ 1` from an initial page `r₀` produces a page at least `r₀`. -/
theorem le_reindexedPage (r₀ r : ℤ) (hr : 1 ≤ r) : r₀ ≤ r₀ + r - 1 := sorry

/-- Consecutive page indices remain consecutive after shifting the initial page. -/
theorem reindexedPage_succ (r₀ : ℤ) {r s : ℤ} (hrs : r + 1 = s) :
    r₀ + r - 1 + 1 = r₀ + s - 1 := sorry

/-- Reindex a cohomological spectral sequence from its initial page as a spectral sequence
starting at page one. -/
@[stacks 0BDU "page-one presentation"]
abbrev ofInitial (E : CohomologicalSpectralSequence C r₀) :
    SpectralSequence C
      (fun r ↦ ComplexShape.up' (⟨r₀ + r - 1, 1 - (r₀ + r - 1)⟩ : ℤ × ℤ)) 1 where
  page r hr := E.page (r₀ + r - 1) (le_reindexedPage r₀ r hr)
  iso r r' pq hrr' hr := E.iso (r₀ + r - 1) (r₀ + r' - 1) pq
    (reindexedPage_succ r₀ hrr') (le_reindexedPage r₀ r hr)

/-- The positive page-one index corresponding to a page `r` of a spectral sequence starting at
`r₀`. -/
theorem index_pos (r₀ r : ℤ) (hr : r₀ ≤ r) :
    0 < Int.toNat (r - r₀ + 1) := sorry

/-- The positive page-one index corresponding to a page `r ≥ r₀`. -/
@[stacks 0BDU "positive reindexed page index"]
def index (r₀ r : ℤ) (hr : r₀ ≤ r) : ℕ+ :=
  ⟨Int.toNat (r - r₀ + 1), index_pos r₀ r hr⟩

end One

namespace Initial

/-- The support of the initial page on the antidiagonal of total degree `n`. -/
@[stacks 0BDU "initial-page antidiagonal support"]
def antidiagonalSupport (E : CohomologicalSpectralSequence C r₀) (n : ℤ) : Set ℤ :=
  {p : ℤ | ¬ IsZero ((E.page r₀).X (p, n - p))}

end Initial
end Page

/-- A successor page is still at least the initial page. -/
theorem le_page_succ {r₀ r : ℤ} (hr : r₀ ≤ r) : r₀ ≤ r + 1 := sorry

namespace Page.One

/-- Reindexing the initial page gives the first positive page. -/
@[simp]
theorem index_initial (r₀ : ℤ) :
    index r₀ r₀ le_rfl = 1 := sorry

/-- Reindexing commutes with advancing to the next page. -/
@[simp]
theorem index_succ {r₀ r : ℤ} (hr : r₀ ≤ r) :
    index r₀ (r + 1) (le_page_succ hr) = index r₀ r hr + 1 := sorry

end Page.One

/-- The cycle piece `Z_r^{p,q}` viewed as a subobject of the initial-page entry. -/
@[stacks 0BDU "cycle filtration from an arbitrary initial page"]
abbrev cycle (E : CohomologicalSpectralSequence C r₀) (pq : ℤ × ℤ)
    (r : ℤ) (hr : r₀ ≤ r) :=
  (Page.One.ofInitial E).cycle pq (Page.One.index r₀ r hr)

/-- The boundary piece `B_r^{p,q}` viewed as a subobject of the initial-page entry. -/
@[stacks 0BDU "boundary filtration from an arbitrary initial page"]
abbrev boundary (E : CohomologicalSpectralSequence C r₀) (pq : ℤ × ℤ)
    (r : ℤ) (hr : r₀ ≤ r) :=
  (Page.One.ofInitial E).boundary pq (Page.One.index r₀ r hr)

/-- A cohomological spectral sequence is regular when every outgoing differential eventually
vanishes at every bidegree. -/
@[stacks 0BDU]
def IsRegular (E : CohomologicalSpectralSequence C r₀) : Prop :=
  ∀ p q : ℤ, ∃ b : ℤ, ∀ ⦃r : ℤ⦄ (hr : r₀ ≤ r), b ≤ r →
    (E.page r).d (p, q) (p + r, q - r + 1) = 0

/-- A cohomological spectral sequence is coregular when every incoming differential eventually
vanishes at every bidegree. -/
@[stacks 0BDU]
def IsCoregular (E : CohomologicalSpectralSequence C r₀) : Prop :=
  ∀ p q : ℤ, ∃ b : ℤ, ∀ ⦃r : ℤ⦄ (hr : r₀ ≤ r), b ≤ r →
    (E.page r).d (p - r, q + r - 1) (p, q) = 0

/-- A cohomological spectral sequence is bounded when every initial-page antidiagonal has finite
support. -/
@[stacks 0BDU]
def IsBounded (E : CohomologicalSpectralSequence C r₀) : Prop :=
  ∀ n : ℤ, (Page.Initial.antidiagonalSupport E n).Finite

/-- A cohomological spectral sequence is bounded below when, on every initial-page antidiagonal,
the entries vanish for all sufficiently large first indices. -/
@[stacks 0BDU]
def IsBoundedBelow (E : CohomologicalSpectralSequence C r₀) : Prop :=
  ∀ n : ℤ, ∃ b : ℤ, ∀ ⦃p : ℤ⦄, b ≤ p → IsZero ((E.page r₀).X (p, n - p))

/-- A cohomological spectral sequence is bounded above when, on every initial-page antidiagonal,
the entries vanish for all sufficiently small first indices. -/
@[stacks 0BDU]
def IsBoundedAbove (E : CohomologicalSpectralSequence C r₀) : Prop :=
  ∀ n : ℤ, ∃ b : ℤ, ∀ ⦃p : ℤ⦄, p ≤ b → IsZero ((E.page r₀).X (p, n - p))

/-- Bounded-below spectral sequences are exactly those whose initial-page antidiagonal supports
are bounded above. -/
theorem isBoundedBelow_iff_bddAbove (E : CohomologicalSpectralSequence C r₀) :
    IsBoundedBelow E ↔ ∀ n : ℤ, BddAbove (Page.Initial.antidiagonalSupport E n) := sorry

/-- Bounded-above spectral sequences are exactly those whose initial-page antidiagonal supports
are bounded below. -/
theorem isBoundedAbove_iff_bddBelow (E : CohomologicalSpectralSequence C r₀) :
    IsBoundedAbove E ↔ ∀ n : ℤ, BddBelow (Page.Initial.antidiagonalSupport E n) := sorry

/-- Regularity is equivalent to eventual stabilization of every cycle piece. -/
@[stacks 0BDV]
theorem IsRegular.iff_eventually_cycle_eq (E : CohomologicalSpectralSequence C r₀) :
    IsRegular E ↔
      ∀ p q : ℤ, ∃ b : ℤ, ∀ ⦃r : ℤ⦄ (hr : r₀ ≤ r), b ≤ r →
        E.cycle (p, q) r hr = E.cycle (p, q) (r + 1) (le_page_succ hr) := sorry

/-- Coregularity is equivalent to eventual stabilization of every boundary piece. -/
@[stacks 0BDV]
theorem IsCoregular.iff_eventually_boundary_eq (E : CohomologicalSpectralSequence C r₀) :
    IsCoregular E ↔
      ∀ p q : ℤ, ∃ b : ℤ, ∀ ⦃r : ℤ⦄ (hr : r₀ ≤ r), b ≤ r →
        E.boundary (p, q) r hr = E.boundary (p, q) (r + 1) (le_page_succ hr) := sorry

/-- A cohomological spectral sequence is bounded exactly when it is bounded below and bounded
above. -/
@[stacks 0BDV]
theorem IsBounded.iff_below_and_above
    (E : CohomologicalSpectralSequence C r₀) :
    IsBounded E ↔ IsBoundedBelow E ∧ IsBoundedAbove E := sorry

/-- Vanishing of an initial-page entry propagates to the same entry on every later page. -/
theorem Page.isZero_of_initial (E : CohomologicalSpectralSequence C r₀)
    {pq : ℤ × ℤ} {r : ℤ} (h₀ : IsZero ((E.page r₀).X pq)) (hr : r₀ ≤ r) :
    IsZero ((E.page r).X pq) := sorry

/-- A bounded-below cohomological spectral sequence is regular. -/
@[stacks 0BDV]
theorem IsBoundedBelow.isRegular {E : CohomologicalSpectralSequence C r₀}
    (hE : IsBoundedBelow E) : IsRegular E := sorry

/-- A bounded-above cohomological spectral sequence is coregular. -/
@[stacks 0BDV]
theorem IsBoundedAbove.isCoregular {E : CohomologicalSpectralSequence C r₀}
    (hE : IsBoundedAbove E) : IsCoregular E := sorry

namespace IsBounded

/-- A bounded cohomological spectral sequence is bounded below. -/
@[stacks 0BDV "lower boundedness of a bounded spectral sequence"]
theorem isBoundedBelow {E : CohomologicalSpectralSequence C r₀}
    (hE : IsBounded E) : IsBoundedBelow E := sorry

/-- A bounded cohomological spectral sequence is bounded above. -/
@[stacks 0BDV "upper boundedness of a bounded spectral sequence"]
theorem isBoundedAbove {E : CohomologicalSpectralSequence C r₀}
    (hE : IsBounded E) : IsBoundedAbove E := sorry

/-- A bounded cohomological spectral sequence is regular. -/
@[stacks 0BDV "regularity of a bounded spectral sequence"]
theorem isRegular {E : CohomologicalSpectralSequence C r₀}
    (hE : IsBounded E) : IsRegular E := sorry

/-- A bounded cohomological spectral sequence is coregular. -/
@[stacks 0BDV "coregularity of a bounded spectral sequence"]
theorem isCoregular {E : CohomologicalSpectralSequence C r₀}
    (hE : IsBounded E) : IsCoregular E := sorry

end IsBounded

section StartsAtZero

/-- A positive page number is a valid page of a cohomological spectral sequence starting at
zero. -/
theorem zero_le_of_one_le {r : ℤ} (hr : 1 ≤ r) : 0 ≤ r := sorry

/-- A bounded cohomological spectral sequence starting at page zero stabilizes at every fixed
bidegree: beyond any prescribed lower bound, some page object is isomorphic to `E∞`. -/
theorem IsBounded.exists_page_iso_infinity
    (E : CohomologicalSpectralSequence C 0) (hbounded : IsBounded E)
    (pq : ℤ × ℤ)
    [CompleteLattice (Subobject ((Page.One.ofZero E).pageObject pq 1))]
    (lower : ℤ) :
    ∃ (N : ℤ) (hN : 1 ≤ N), lower ≤ N ∧
      Nonempty
        (((E.page N (zero_le_of_one_le hN)).X pq) ≅
          (Page.One.ofZero E).infinityPage pq) := sorry

end StartsAtZero

end CohomologicalSpectralSequence
end CategoryTheory
