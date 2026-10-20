/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Homology.SpectralSequence.PageFiltration
import StacksCheckRecall

@[expose] public section

open CategoryTheory.Limits

noncomputable section

universe u v

namespace CategoryTheory

open scoped SpectralSequence

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {κ : Type*} {c : ℤ → ComplexShape κ}
variable (E : SpectralSequence C c 1) (pq : κ) (r : ℕ+)

/-!
# Compatibility entry for Definition 12.20.2

The reusable cycle and boundary filtration of a spectral sequence lives in
`ReasLib.CategoryTheory.Homology.SpectralSequence.PageFiltration`.
-/

/- Definition 12.20.2 (011O): a spectral sequence has descending cycle pieces `Z_r`, ascending
boundary pieces `B_r`, page quotients `Z_r / B_r`, eventual pieces `Z_∞` and `B_∞`, and a
degeneration predicate. -/
@[stacks 011O]
#check (E.cycle pq r : Subobject (E⟦1, pq⟧))

#check (E.positivePage r : HomologicalComplex C (c (r : ℤ)))
#check SpectralSequence.Hom.positivePage
#check (SpectralSequence.positivePageFunctor c r)
#check (SpectralSequence.PositivePage.cycles E pq r)
#check (SpectralSequence.PositivePage.boundaries E pq r)
#check (SpectralSequence.PositivePage.cyclesToNext E pq r)
#check (E.boundary pq r : Subobject (E⟦1, pq⟧))
#check (E.boundary_le_cycle pq r : E.boundary pq r ≤ E.cycle pq r)
#check (E.cycleToPage pq r : (E.cycle pq r : C) ⟶ E⟦r, pq⟧)
#check (E.homologyPageTower pq : HomologyPageTower C)
#check (SpectralSequence.HomologyTower.functor (C := C) (c := c) pq)
#check (HomologyPageTower.pageQuotient (E.homologyPageTower pq) r : C)
#check (HomologyPageTower.PageQuotient.toPage (E.homologyPageTower pq) r
  (HomologyPageTower.Boundary.intersection_toPage_zero (E.homologyPageTower pq) r))
#check (HomologyPageTower.PageQuotient.toPage_proof_irrel (E.homologyPageTower pq) r
  (HomologyPageTower.Boundary.intersection_toPage_zero (E.homologyPageTower pq) r)
  (HomologyPageTower.Boundary.intersection_toPage_zero (E.homologyPageTower pq) r))
#check @HomologyPageTower.PageQuotient.IsToPage
#check @HomologyPageTower.PageQuotient.toPage_isToPage
#check @HomologyPageTower.PageQuotient.IsToPage.unique
#check (HomologyPageTower.PageQuotient.isIsomorphicCokernel (E.homologyPageTower pq) r)
#check (HomologyPageTower.PageQuotient.isIsomorphic (E.homologyPageTower pq) r)
#check (HomologyPageTower.PageHomology.Functor.iso C r)

section InfinityPage

variable [CompleteLattice (Subobject E⟦1,pq⟧)]

#check (E.cycleInfinity pq : Subobject (E⟦1, pq⟧))
#check (E.boundaryInfinity pq : Subobject (E⟦1, pq⟧))
#check (E.infinityPage pq : C)
#check (SpectralSequence.InfinityPage.π E pq :
  (E.cycleInfinity pq : C) ⟶ E.infinityPage pq)
#check (SpectralSequence.InfinityPage.isIsomorphic E pq)

end InfinityPage

#check (E.degeneratesAt r : Prop)

end CategoryTheory
