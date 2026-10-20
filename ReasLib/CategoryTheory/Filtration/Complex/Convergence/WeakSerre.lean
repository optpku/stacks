/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Complex.Convergence
public import ReasLib.CategoryTheory.Filtration.WeakSerre
public import ReasLib.CategoryTheory.Homology.SpectralSequence.WeakSerre

/-!
# Weak-Serre Devissage for Convergent Filtered Complexes

This leaf extends the core convergence API with closure results for weak Serre classes.  Keeping
these results separate prevents basic convergence consumers from importing devissage machinery.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty

noncomputable section

universe u v

namespace CategoryTheory
namespace FilteredComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace HasFiniteFiltrations

variable {K : FilteredComplex C} {E : CohomologicalSpectralSequence C 0}

/-- Finite term filtrations make the generic explicit-limit-stage weak-Serre result applicable to
an associated spectral sequence. -/
@[stacks 012W "weak Serre devissage along a convergent spectral sequence"]
theorem Convergence.infinityPage_mem_of_page_mem (hfinite : K.HasFiniteFiltrations)
    (hAssoc : FilteredComplex.IsAssociated K E)
    (L : SpectralSequence.LimitStages (CohomologicalSpectralSequence.Page.One.ofZero E))
    (P : ObjectProperty C) [IsWeakSerreClass P]
    {r : ℤ} (hr : 0 ≤ r) (hpage : ∀ p q : ℤ, P ((E.page r hr).X (p, q)))
    (p q : ℤ) : P (L.infinityPage (p, q)) := sorry

/-- Pagewise weak-Serre membership propagates to every graded piece of the induced cohomology
filtration. -/
@[stacks 012W "weak Serre devissage along a convergent spectral sequence"]
theorem Cohomology.gradedPiece_mem_of_page_mem (hfinite : K.HasFiniteFiltrations)
    (hAssoc : FilteredComplex.IsAssociated K E)
    (P : ObjectProperty C) [IsWeakSerreClass P] {r : ℤ} (hr : 0 ≤ r)
    (hpage : ∀ p q : ℤ, P ((E.page r hr).X (p, q))) (n p : ℤ) :
    P ((K.inducedCohomologyFiltration n).gradedPiece p) := sorry

/-- If one page lies in a weak Serre class, finite term filtrations imply that every cohomology
object lies in that class. -/
@[stacks 012W "weak Serre devissage along a convergent spectral sequence"]
theorem Cohomology.mem_of_page_mem (hfinite : K.HasFiniteFiltrations)
    (hAssoc : FilteredComplex.IsAssociated K E)
    (P : ObjectProperty C) [IsWeakSerreClass P] {r : ℤ} (hr : 0 ≤ r)
    (hpage : ∀ p q : ℤ, P ((E.page r hr).X (p, q))) :
    ∀ n : ℤ, P (K.underlying.homology n) := sorry

end HasFiniteFiltrations
end FilteredComplex
end CategoryTheory
