/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Homology.SpectralSequence.Bounded
public import ReasLib.CategoryTheory.Homology.SpectralSequence.LimitStages
public import ReasLib.CategoryTheory.ObjectProperty.WeakSerre

/-!
# Weak Serre Classes and Spectral Sequences

This file contains the representation-independent propagation of a weak Serre property through
the pages of a bounded cohomological spectral sequence and into its infinity page.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty

noncomputable section

universe u v

namespace CategoryTheory
namespace CohomologicalSpectralSequence

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A successor of a nonnegative page is nonnegative. -/
theorem zero_le_page_succ {r : ℤ} (hr : 0 ≤ r) : 0 ≤ r + 1 := sorry

/-- If every entry of one page lies in a weak Serre class, then every entry of the successor page
lies in that class. -/
theorem pageSucc_mem (E : CohomologicalSpectralSequence C 0)
    (P : ObjectProperty C) [IsWeakSerreClass P] {r : ℤ} (hr : 0 ≤ r)
    (hpage : ∀ p q : ℤ, P ((E.page r hr).X (p, q))) :
    ∀ p q : ℤ, P ((E.page (r + 1) (zero_le_page_succ hr)).X (p, q)) := sorry

/-- Weak Serre membership of every entry propagates from a page to every later page. -/
theorem page_mem_of_le (E : CohomologicalSpectralSequence C 0)
    (P : ObjectProperty C) [IsWeakSerreClass P] {r N : ℤ} (hr : 0 ≤ r)
    (hpage : ∀ p q : ℤ, P ((E.page r hr).X (p, q))) (h_le : r ≤ N) :
    ∀ p q : ℤ, P ((E.page N (hr.trans h_le)).X (p, q)) := sorry

section CanonicalInfinityPage

/-- If every entry of one page of a bounded cohomological spectral sequence lies in a weak Serre
class, then every infinity-page entry lies in that class. -/
@[stacks 012W "weak Serre membership on a bounded spectral sequence"]
theorem infinityPage_mem_of_page_mem (E : CohomologicalSpectralSequence C 0)
    (P : ObjectProperty C) [IsWeakSerreClass P] (hbounded : E.IsBounded)
    {r : ℤ} (hr : 0 ≤ r) (hpage : ∀ p q : ℤ, P ((E.page r hr).X (p, q)))
    (p q : ℤ)
    [CompleteLattice (Subobject ((Page.One.ofZero E).pageObject (p, q) 1))] :
    P ((Page.One.ofZero E).infinityPage (p, q)) := sorry

end CanonicalInfinityPage

namespace LimitStages

/-- Weak Serre membership of a page propagates to the infinity-page representative selected by
arbitrary explicit limit stages of a bounded cohomological spectral sequence. -/
@[stacks 012W "weak Serre membership on an explicit infinity page"]
theorem infinityPage_mem_of_page_mem (E : CohomologicalSpectralSequence C 0)
    (L : SpectralSequence.LimitStages (Page.One.ofZero E))
    (P : ObjectProperty C) [IsWeakSerreClass P] (hbounded : E.IsBounded)
    {r : ℤ} (hr : 0 ≤ r) (hpage : ∀ p q : ℤ, P ((E.page r hr).X (p, q)))
    (p q : ℤ) :
    P (L.infinityPage (p, q)) := sorry

end LimitStages

end CohomologicalSpectralSequence
end CategoryTheory
