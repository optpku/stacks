/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Homology.SpectralSequence.Shifted.UnitShift
import StacksCheckRecall

@[expose] public section

open CategoryTheory.Limits

noncomputable section

universe v u

namespace CategoryTheory

variable {A : Type u} [Category.{v} A] [Abelian A]
variable (T : ℕ+ → (A ≌ A)) (S : ShiftedSpectralSequence T) (r : ℕ+)
variable {S' : ShiftedSpectralSequence T} (f : S ⟶ S')

/- Remark 12.20.3 (Variant) (tag `0AMI`): the shift may vary with the page. A page is a shifted
differential object for `T r`; its homology is the next page, morphisms commute with these
identifications, and the usual cycle and boundary filtrations and page quotients remain available.
-/
@[stacks 0AMI]
#check (ShiftedSpectralSequence T)

#check (S.page r : ShiftedDifferentialObject (T r).functor)
#check (S.iso r : (S.page r).homology ≅ (S.page (r + 1)).obj)
#check (f : S ⟶ S')
#check (inferInstance : Category (ShiftedSpectralSequence T))
#check (ShiftedSpectralSequence.pageFunctor T r)
#check (ShiftedSpectralSequence.Page.homologyIso T r)
#check (S.homologyPageTower : HomologyPageTower A)
#check (ShiftedSpectralSequence.HomologyTower.functor T)
#check (HomologyPageTower.PageHomology.iso S.homologyPageTower r)
#check (HomologyPageTower.PageHomology.Functor.iso A r)

#check (ShiftedSpectralSequence.Page.cycles S r : Subobject (S.page r).obj)
#check (ShiftedSpectralSequence.Page.boundaries S r : Subobject (S.page r).obj)
#check (S.cycle r : Subobject (S.page 1).obj)
#check (S.boundary r : Subobject (S.page 1).obj)
#check (S.boundary_le_cycle r : S.boundary r ≤ S.cycle r)
#check (S.cycleToPage r : (S.cycle r : A) ⟶ (S.page r).obj)
#check (HomologyPageTower.pageQuotient S.homologyPageTower r : A)
#check (HomologyPageTower.PageQuotient.toPage S.homologyPageTower r
  (HomologyPageTower.Boundary.intersection_toPage_zero S.homologyPageTower r))
#check (HomologyPageTower.PageQuotient.toPage_proof_irrel S.homologyPageTower r
  (HomologyPageTower.Boundary.intersection_toPage_zero S.homologyPageTower r)
  (HomologyPageTower.Boundary.intersection_toPage_zero S.homologyPageTower r))
#check @HomologyPageTower.PageQuotient.IsToPage
#check @HomologyPageTower.PageQuotient.toPage_isToPage
#check @HomologyPageTower.PageQuotient.IsToPage.unique
#check (HomologyPageTower.PageQuotient.isIsomorphicCokernel S.homologyPageTower r)
#check (HomologyPageTower.PageQuotient.isIsomorphic S.homologyPageTower r)
#check (HomologyPageTower.PageHomology.map
  (ShiftedSpectralSequence.HomologyTower.map f) r)
#check @HomologyPageTower.PageHomology.IsInduced
#check @HomologyPageTower.PageHomology.map_isInduced
#check @HomologyPageTower.PageHomology.IsInduced.unique
#check (HomologyPageTower.Cycle.map
  (ShiftedSpectralSequence.HomologyTower.map f) r)
#check (HomologyPageTower.Boundary.map
  (ShiftedSpectralSequence.HomologyTower.map f) r)
#check (HomologyPageTower.PageQuotient.map
  (ShiftedSpectralSequence.HomologyTower.map f) r)
#check (HomologyPageTower.PageQuotient.π_naturality
  (ShiftedSpectralSequence.HomologyTower.map f) r)
#check @HomologyPageTower.PageQuotient.IsInduced
#check @HomologyPageTower.PageQuotient.map_isInduced
#check @HomologyPageTower.PageQuotient.IsInduced.unique
#check (ShiftedSpectralSequence.Cycle.toPage_naturality f r)

section InfinityPage

variable [CompleteLattice (Subobject (S.page 1).obj)]

#check (S.cycleInfinity : Subobject (S.page 1).obj)
#check (S.boundaryInfinity : Subobject (S.page 1).obj)
#check (S.infinityPage : A)
#check (ShiftedSpectralSequence.InfinityPage.π S :
  (S.cycleInfinity : A) ⟶ S.infinityPage)
#check (ShiftedSpectralSequence.InfinityPage.isIsomorphic S)

end InfinityPage

section UnitShift

variable [HasShift A ℤ]
variable (U : ShiftedSpectralSequence
  (fun _ : ℕ+ ↦ (shiftFunctor A (1 : ℤ)).asEquivalence))

#check (U.toSpectralSequence : SpectralSequence A (fun _ : ℤ ↦ ComplexShape.up ℤ) 1)
#check (U.pageZeroIso r)

end UnitShift

end CategoryTheory
