/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Homology.SpectralSequence.PositivePage
public import ReasLib.CategoryTheory.Homology.PageTower
public import ReasLib.CategoryTheory.Homology.ShortComplex.Cycles

/-!
# Page Filtrations of Spectral Sequences

Each graded entry of a spectral sequence determines a `HomologyPageTower`.  The cycle and
boundary filtrations, page quotients, and infinity page in this module are the graded-entry
specializations of the neutral tower API.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace SpectralSequence

variable {κ : Type*} {c : ℤ → ComplexShape κ}

open scoped SpectralSequence

namespace PositivePage

/-- The cycles subobject on positive page `r` at grading `pq`. -/
@[stacks 011O "positive-page cycle owner"]
abbrev cycles
    (E : SpectralSequence C c 1) (pq : κ) (r : ℕ+) : Subobject E⟦r, pq⟧ :=
  kernelSubobject ((E.positivePage r).dFrom pq)

/-- The boundaries subobject on positive page `r` at grading `pq`. -/
@[stacks 011O "positive-page boundary owner"]
abbrev boundaries
    (E : SpectralSequence C c 1) (pq : κ) (r : ℕ+) : Subobject E⟦r, pq⟧ :=
  imageSubobject ((E.positivePage r).dTo pq)

/-- The page boundaries are contained in the page cycles. -/
theorem boundaries_le_cycles
    (E : SpectralSequence C c 1) (pq : κ) (r : ℕ+) :
    boundaries E pq r ≤ cycles E pq r := sorry

/-- The canonical map from cycles on page `r` to the entry on page `r + 1`. -/
@[stacks 011O "positive-page transition"]
noncomputable def cyclesToNext
    (E : SpectralSequence C c 1) (pq : κ) (r : ℕ+) :
    (cycles E pq r : C) ⟶ E⟦r + 1, pq⟧ :=
  ShortComplex.Cycles.toHomology ((E.positivePage r).sc pq) ≫
    (PositivePage.homologyIso E pq r).hom

/-- Page boundaries vanish under the canonical map to the next page. -/
theorem boundaries_toNext_zero
    (E : SpectralSequence C c 1) (pq : κ) (r : ℕ+) :
    Subobject.ofLE (boundaries E pq r) (cycles E pq r) (boundaries_le_cycles E pq r) ≫
      cyclesToNext E pq r = 0 := sorry

/-- The quotient of page cycles by page boundaries is canonically the next page entry. -/
@[stacks 011O "positive-page quotient comparison"]
theorem quotientToNext_isIso
    (E : SpectralSequence C c 1) (pq : κ) (r : ℕ+) :
    IsIso
      (cokernel.desc
        (Subobject.ofLE (boundaries E pq r) (cycles E pq r) (boundaries_le_cycles E pq r))
        (cyclesToNext E pq r) (boundaries_toNext_zero E pq r)) := sorry

end PositivePage

/-- The homology page tower associated to a fixed grading of a spectral sequence. -/
@[stacks 011O]
noncomputable def homologyPageTower (E : SpectralSequence C c 1) (pq : κ) :
    HomologyPageTower C where
  page r := E⟦r, pq⟧
  pageCycle r := PositivePage.cycles E pq r
  pageBoundary r := PositivePage.boundaries E pq r
  pageBoundary_le_pageCycle r := PositivePage.boundaries_le_cycles E pq r
  toNext r := PositivePage.cyclesToNext E pq r
  pageBoundary_toNext_zero r := PositivePage.boundaries_toNext_zero E pq r
  isIso_descToNext r := PositivePage.quotientToNext_isIso E pq r

namespace HomologyTower

/-- The `r`-th object of the homology page tower is the corresponding spectral-sequence entry. -/
@[simp, stacks 011O "homology tower page bridge"]
theorem page (E : SpectralSequence C c 1) (pq : κ) (r : ℕ+) :
    (E.homologyPageTower pq).page r = E⟦r, pq⟧ := sorry

/-- The cycle subobject of the homology page tower is the kernel of the outgoing page
differential. -/
@[simp, stacks 011O "homology tower cycle bridge"]
theorem pageCycle (E : SpectralSequence C c 1) (pq : κ) (r : ℕ+) :
    (E.homologyPageTower pq).pageCycle r = PositivePage.cycles E pq r := sorry

/-- The boundary subobject of the homology page tower is the image of the incoming page
differential. -/
@[simp, stacks 011O "homology tower boundary bridge"]
theorem pageBoundary (E : SpectralSequence C c 1) (pq : κ) (r : ℕ+) :
    (E.homologyPageTower pq).pageBoundary r = PositivePage.boundaries E pq r := sorry

/-- The next-page map of the homology page tower is the canonical map from page cycles to the
following page. -/
@[simp, stacks 011O "homology tower transition bridge"]
theorem toNext (E : SpectralSequence C c 1) (pq : κ) (r : ℕ+) :
    (E.homologyPageTower pq).toNext r = PositivePage.cyclesToNext E pq r := sorry

namespace Map

/-- A spectral-sequence morphism preserves the page cycles at a fixed grading. -/
theorem pageCycle_factors
    {E E' : SpectralSequence C c 1} (f : E ⟶ E') (pq : κ) (r : ℕ+) :
    ((E'.homologyPageTower pq).pageCycle r).Factors
      (((E.homologyPageTower pq).pageCycle r).arrow ≫
        (f.positivePage r).f pq) := sorry

/-- A spectral-sequence morphism preserves the page boundaries at a fixed grading. -/
theorem pageBoundary_factors
    {E E' : SpectralSequence C c 1} (f : E ⟶ E') (pq : κ) (r : ℕ+) :
    ((E'.homologyPageTower pq).pageBoundary r).Factors
      (((E.homologyPageTower pq).pageBoundary r).arrow ≫
        (f.positivePage r).f pq) := sorry

/-- The restricted cycle maps of a spectral-sequence morphism commute with passage to the next
page. -/
theorem toNext_comm
    {E E' : SpectralSequence C c 1} (f : E ⟶ E') (pq : κ) (r : ℕ+) :
    ((E'.homologyPageTower pq).pageCycle r).factorThru
        (((E.homologyPageTower pq).pageCycle r).arrow ≫
          (f.positivePage r).f pq)
        (pageCycle_factors f pq r) ≫
        (E'.homologyPageTower pq).toNext r =
      (E.homologyPageTower pq).toNext r ≫
        (f.positivePage (r + 1)).f pq := sorry

/-- The restricted boundary and cycle maps commute with the page-boundary inclusion.  This is a
law field of the induced homology-page-tower morphism, keeping quotient maps concrete without
depending on a deferred global theorem. -/
theorem pageBoundary_map_comp_ofLE
    {E E' : SpectralSequence C c 1} (f : E ⟶ E') (pq : κ) (r : ℕ+) :
    Subobject.ofLE
        ((E.homologyPageTower pq).pageBoundary r)
        ((E.homologyPageTower pq).pageCycle r)
        ((E.homologyPageTower pq).pageBoundary_le_pageCycle r) ≫
      ((E'.homologyPageTower pq).pageCycle r).factorThru
        (((E.homologyPageTower pq).pageCycle r).arrow ≫
          (f.positivePage r).f pq)
        (pageCycle_factors f pq r) =
      ((E'.homologyPageTower pq).pageBoundary r).factorThru
        (((E.homologyPageTower pq).pageBoundary r).arrow ≫
          (f.positivePage r).f pq)
        (pageBoundary_factors f pq r) ≫
      Subobject.ofLE
        ((E'.homologyPageTower pq).pageBoundary r)
        ((E'.homologyPageTower pq).pageCycle r)
        ((E'.homologyPageTower pq).pageBoundary_le_pageCycle r) := sorry

/-- A spectral-sequence morphism preserves the recursive cycle stage in the first page. -/
theorem cycle_factors
    {E E' : SpectralSequence C c 1} (f : E ⟶ E') (pq : κ) (r : ℕ+) :
    ((E'.homologyPageTower pq).cycle r).Factors
      (((E.homologyPageTower pq).cycle r).arrow ≫
        (f.positivePage 1).f pq) := sorry

/-- A spectral-sequence morphism preserves the recursive boundary stage in the first page. -/
theorem boundary_factors
    {E E' : SpectralSequence C c 1} (f : E ⟶ E') (pq : κ) (r : ℕ+) :
    ((E'.homologyPageTower pq).boundary r).Factors
      (((E.homologyPageTower pq).boundary r).arrow ≫
        (f.positivePage 1).f pq) := sorry

/-- The recursively restricted boundary and cycle maps commute with the inclusion `B_r ↪ Z_r`. -/
theorem boundary_map_comp_ofLE
    {E E' : SpectralSequence C c 1} (f : E ⟶ E') (pq : κ) (r : ℕ+) :
    Subobject.ofLE
        ((E.homologyPageTower pq).boundary r)
        ((E.homologyPageTower pq).cycle r)
        ((E.homologyPageTower pq).boundary_le_cycle r) ≫
      ((E'.homologyPageTower pq).cycle r).factorThru
        (((E.homologyPageTower pq).cycle r).arrow ≫
          (f.positivePage 1).f pq)
        (cycle_factors f pq r) =
      ((E'.homologyPageTower pq).boundary r).factorThru
        (((E.homologyPageTower pq).boundary r).arrow ≫
          (f.positivePage 1).f pq)
        (boundary_factors f pq r) ≫
      Subobject.ofLE
        ((E'.homologyPageTower pq).boundary r)
        ((E'.homologyPageTower pq).cycle r)
        ((E'.homologyPageTower pq).boundary_le_cycle r) := sorry

/-- A spectral-sequence morphism preserves the recursive boundary-cycle intersection in the
first page. -/
theorem intersection_factors
    {E E' : SpectralSequence C c 1} (f : E ⟶ E') (pq : κ) (r : ℕ+) :
    ((E'.homologyPageTower pq).boundary r ⊓
      (E'.homologyPageTower pq).cycle r).Factors
      (((E.homologyPageTower pq).boundary r ⊓
        (E.homologyPageTower pq).cycle r).arrow ≫
          (f.positivePage 1).f pq) := sorry

/-- The restricted recursive intersection and cycle maps of a spectral-sequence morphism
commute with the inclusion into the cycle stage. -/
theorem intersection_map_comp_ofLE
    {E E' : SpectralSequence C c 1} (f : E ⟶ E') (pq : κ) (r : ℕ+) :
    Subobject.ofLE
        ((E.homologyPageTower pq).boundary r ⊓ (E.homologyPageTower pq).cycle r)
        ((E.homologyPageTower pq).cycle r)
        _root_.inf_le_right ≫
      ((E'.homologyPageTower pq).cycle r).factorThru
        (((E.homologyPageTower pq).cycle r).arrow ≫ (f.positivePage 1).f pq)
        (cycle_factors f pq r) =
      ((E'.homologyPageTower pq).boundary r ⊓ (E'.homologyPageTower pq).cycle r).factorThru
        (((E.homologyPageTower pq).boundary r ⊓ (E.homologyPageTower pq).cycle r).arrow ≫
          (f.positivePage 1).f pq)
        (intersection_factors f pq r) ≫
      Subobject.ofLE
        ((E'.homologyPageTower pq).boundary r ⊓ (E'.homologyPageTower pq).cycle r)
        ((E'.homologyPageTower pq).cycle r)
        _root_.inf_le_right := sorry

end Map

/-- The morphism of homology page towers induced at a fixed grading by a spectral-sequence
morphism. -/
@[stacks 011O "homology-page tower morphism"]
noncomputable def map
    {E E' : SpectralSequence C c 1} (f : E ⟶ E') (pq : κ) :
    E.homologyPageTower pq ⟶ E'.homologyPageTower pq where
  app r := (f.positivePage r).f pq
  pageCycle_factors r := Map.pageCycle_factors f pq r
  pageBoundary_factors r := Map.pageBoundary_factors f pq r
  toNext_comm r := Map.toNext_comm f pq r
  pageBoundary_map_comp_ofLE r := Map.pageBoundary_map_comp_ofLE f pq r
  cycle_factors r := Map.cycle_factors f pq r
  boundary_factors r := Map.boundary_factors f pq r
  boundary_map_comp_ofLE r := Map.boundary_map_comp_ofLE f pq r
  intersection_factors r := Map.intersection_factors f pq r
  intersection_map_comp_ofLE r := Map.intersection_map_comp_ofLE f pq r

/-- The component of the induced homology-page-tower map is the corresponding component of the
spectral-sequence morphism. -/
@[simp]
theorem map_app
    {E E' : SpectralSequence C c 1} (f : E ⟶ E') (pq : κ) (r : ℕ+) :
    (map f pq).app r =
      (f.positivePage r).f pq := sorry

/-- The induced tower map preserves identity morphisms. -/
theorem map_id (E : SpectralSequence C c 1) (pq : κ) :
    map (𝟙 E) pq = 𝟙 (E.homologyPageTower pq) := sorry

/-- The induced tower map preserves composition. -/
theorem map_comp
    {E E' E'' : SpectralSequence C c 1} (f : E ⟶ E') (g : E' ⟶ E'') (pq : κ) :
    map (f ≫ g) pq = map f pq ≫ map g pq := sorry

section Functor

/-- At a fixed grading, a spectral sequence determines a homology page tower functorially. -/
@[stacks 011O "homology-page tower functor"]
noncomputable def functor (pq : κ) :
  SpectralSequence C c 1 ⥤ HomologyPageTower C where
  obj E := E.homologyPageTower pq
  map f := HomologyTower.map f pq
  map_id E := HomologyTower.map_id E pq
  map_comp f g := HomologyTower.map_comp f g pq

namespace Functor

/-- Evaluation of the homology-page-tower functor on a spectral sequence is its fixed-grading
homology page tower. -/
@[simp]
theorem obj (pq : κ) (E : SpectralSequence C c 1) :
    (functor pq).obj E = E.homologyPageTower pq := sorry

/-- Evaluation of the homology-page-tower functor on a morphism is the induced tower map. -/
@[simp]
theorem map (pq : κ)
    {E E' : SpectralSequence C c 1} (f : E ⟶ E') :
    (functor pq).map f = map f pq := sorry

end Functor

end Functor

end HomologyTower

/-- A zero-based recursive cycle stage for the graded entry `pq`. -/
abbrev CycleStage (E : SpectralSequence C c 1) (pq : κ) (n : ℕ) :=
  HomologyPageTower.CycleStage (E.homologyPageTower pq) n

/-- The recursively constructed cycle stages for the graded entry `pq`. -/
noncomputable abbrev cycleStage (E : SpectralSequence C c 1) (pq : κ) (n : ℕ) :
    CycleStage E pq n :=
  (E.homologyPageTower pq).cycleStage n

/-- The zero-based cycle stage inside `E_1^{pq}`. -/
abbrev stageCycle (E : SpectralSequence C c 1) (pq : κ) (n : ℕ) :
    Subobject E⟦1, pq⟧ :=
  (E.cycleStage pq n).cycle

/-- The canonical map from the zero-based cycle stage to its page entry. -/
noncomputable abbrev stageToPage (E : SpectralSequence C c 1) (pq : κ) (n : ℕ) :
    (E.stageCycle pq n : C) ⟶ (E.pageComplex n).X pq :=
  (E.cycleStage pq n).toPage

/-- The recursively defined cycle subobject `Z_r^{pq} ≤ E_1^{pq}`. -/
@[stacks 011O]
abbrev cycle (E : SpectralSequence C c 1) (pq : κ) (r : ℕ+) :
    Subobject E⟦1, pq⟧ :=
  (E.homologyPageTower pq).cycle r

/-- The recursively defined boundary subobject `B_r^{pq} ≤ E_1^{pq}`. -/
@[stacks 011O]
abbrev boundary (E : SpectralSequence C c 1) (pq : κ) (r : ℕ+) :
    Subobject E⟦1, pq⟧ :=
  (E.homologyPageTower pq).boundary r

/-- On the first page, the cycle subobject is everything. -/
@[stacks 011O]
theorem cycle_one (E : SpectralSequence C c 1) (pq : κ) :
    E.cycle pq 1 = (⊤ : Subobject E⟦1, pq⟧) := sorry

/-- On the first page, the boundary subobject is trivial. -/
@[stacks 011O]
theorem boundary_one (E : SpectralSequence C c 1) (pq : κ) :
    E.boundary pq 1 = (⊥ : Subobject E⟦1, pq⟧) := sorry

/-- Boundaries are contained in cycles on every page. -/
@[stacks 011O]
theorem boundary_le_cycle (E : SpectralSequence C c 1) (pq : κ) (r : ℕ+) :
    E.boundary pq r ≤ E.cycle pq r := sorry

/-- The canonical map `Z_r^{pq} ⟶ E_r^{pq}`. -/
@[stacks 011O]
noncomputable abbrev cycleToPage (E : SpectralSequence C c 1) (pq : κ) (r : ℕ+) :
    (E.cycle pq r : C) ⟶ E⟦r, pq⟧ :=
  (E.homologyPageTower pq).cycleToPage r

/-- On the first page, `cycleToPage` is the cycle inclusion. -/
@[stacks 011O]
theorem Cycle.toPage_one (E : SpectralSequence C c 1) (pq : κ) :
    E.cycleToPage pq 1 = (E.cycle pq 1).arrow := sorry

namespace Cycle

/-- The successor cycle is the pullback of the page cycles along `cycleToPage`. -/
@[stacks 011O]
theorem succ_eq_pullback
    (E : SpectralSequence C c 1) (pq : κ) (r : ℕ+) :
    E.cycle pq (r + 1) =
      (Subobject.map (E.cycle pq r).arrow).obj
        ((Subobject.pullback (E.cycleToPage pq r)).obj
          (kernelSubobject ((E.positivePage r).dFrom pq))) := sorry

end Cycle

namespace Boundary

/-- The successor boundary is the pullback of the page boundaries along `cycleToPage`. -/
@[stacks 011O]
theorem succ_eq_pullback
    (E : SpectralSequence C c 1) (pq : κ) (r : ℕ+) :
    E.boundary pq (r + 1) =
      (Subobject.map (E.cycle pq r).arrow).obj
        ((Subobject.pullback (E.cycleToPage pq r)).obj
          (imageSubobject ((E.positivePage r).dTo pq))) := sorry

end Boundary

/-- Every zero-based recursive stage map is an epimorphism. -/
instance stageToPage_epi (E : SpectralSequence C c 1) (pq : κ) (n : ℕ) :
    Epi (E.stageToPage pq n) := sorry

/-- The canonical map `Z_r^{pq} ⟶ E_r^{pq}` is an epimorphism. -/
instance Cycle.toPage_epi (E : SpectralSequence C c 1) (pq : κ) (r : ℕ+) :
    Epi (E.cycleToPage pq r) := sorry

/-- The recursive map to page `r` kills the included boundary subobject. -/
@[stacks 011O]
theorem Boundary.toPage_zero (E : SpectralSequence C c 1) (pq : κ) (r : ℕ+) :
    Subobject.ofLE (E.boundary pq r) (E.cycle pq r) (E.boundary_le_cycle pq r) ≫
      E.cycleToPage pq r = 0 := sorry

/-- Successor cycle pieces form a descending chain. -/
@[stacks 011O]
theorem Cycle.succ_le (E : SpectralSequence C c 1) (pq : κ) (r : ℕ+) :
    E.cycle pq (r + 1) ≤ E.cycle pq r := sorry

/-- Successor boundary pieces form an ascending chain. -/
@[stacks 011O]
theorem Boundary.le_succ
    (E : SpectralSequence C c 1) (pq : κ) (r : ℕ+) :
    E.boundary pq r ≤ E.boundary pq (r + 1) := sorry

/-- The boundary filtration is monotone in the page index. -/
@[stacks 011O]
theorem Boundary.monotone (E : SpectralSequence C c 1) (pq : κ) :
    ∀ ⦃r s : ℕ+⦄, r ≤ s → E.boundary pq r ≤ E.boundary pq s := sorry

/-- The cycle filtration is antitone in the page index. -/
@[stacks 011O]
theorem Cycle.antitone (E : SpectralSequence C c 1) (pq : κ) :
    ∀ ⦃r s : ℕ+⦄, r ≤ s → E.cycle pq s ≤ E.cycle pq r := sorry

/-- Every boundary stage lies in every cycle stage. -/
@[stacks 011O]
theorem Boundary.le_cycle
    (E : SpectralSequence C c 1) (pq : κ) (r s : ℕ+) :
    E.boundary pq r ≤ E.cycle pq s := sorry

/-- A spectral-sequence morphism maps cycle stages into cycle stages. -/
theorem Cycle.map_le {E E' : SpectralSequence C c 1} (f : E ⟶ E') (pq : κ) (r : ℕ+) :
    (Subobject.exists ((f.positivePage 1).f pq)).obj
      (E.cycle pq r) ≤ E'.cycle pq r := sorry

/-- A spectral-sequence morphism maps boundary stages into boundary stages. -/
theorem Boundary.map_le
    {E E' : SpectralSequence C c 1} (f : E ⟶ E') (pq : κ) (r : ℕ+) :
    (Subobject.exists ((f.positivePage 1).f pq)).obj
      (E.boundary pq r) ≤ E'.boundary pq r := sorry

/-- The map induced by a spectral-sequence morphism between cycle stages. -/
noncomputable def Cycle.map
    {E E' : SpectralSequence C c 1} (f : E ⟶ E') (pq : κ) (r : ℕ+) :
    (E.cycle pq r : C) ⟶ (E'.cycle pq r : C) :=
  HomologyPageTower.Cycle.map (HomologyTower.map f pq) r

/-- The map induced by a spectral-sequence morphism between boundary stages. -/
noncomputable def Boundary.map
    {E E' : SpectralSequence C c 1} (f : E ⟶ E') (pq : κ) (r : ℕ+) :
    (E.boundary pq r : C) ⟶ (E'.boundary pq r : C) :=
  HomologyPageTower.Boundary.map (HomologyTower.map f pq) r

/-- The induced cycle map recovers the first-page component after inclusion. -/
@[reassoc (attr := simp)]
theorem Cycle.map_arrow
    {E E' : SpectralSequence C c 1} (f : E ⟶ E') (pq : κ) (r : ℕ+) :
    Cycle.map f pq r ≫ (E'.cycle pq r).arrow =
      (E.cycle pq r).arrow ≫
        (f.positivePage 1).f pq := sorry

/-- The induced boundary map recovers the first-page component after inclusion. -/
@[reassoc (attr := simp)]
theorem Boundary.map_arrow
    {E E' : SpectralSequence C c 1} (f : E ⟶ E') (pq : κ) (r : ℕ+) :
    Boundary.map f pq r ≫ (E'.boundary pq r).arrow =
      (E.boundary pq r).arrow ≫
        (f.positivePage 1).f pq := sorry

/-- The induced cycle map commutes with the canonical maps to page `r`. -/
@[reassoc]
theorem Cycle.toPage_naturality
    {E E' : SpectralSequence C c 1} (f : E ⟶ E') (pq : κ) (r : ℕ+) :
    Cycle.map f pq r ≫ E'.cycleToPage pq r =
      E.cycleToPage pq r ≫
        (f.positivePage r).f pq := sorry

section Infinity

variable [LocallySmall.{v} C] [WellPowered.{v} C]
  [HasWidePullbacks.{v} C] [HasCoproducts.{v} C]

/-- The eventual cycle subobject `Z_infinity^{pq}`. -/
@[stacks 011O]
noncomputable abbrev cycleInfinity (E : SpectralSequence C c 1) (pq : κ)
    : Subobject E⟦1, pq⟧ :=
  HomologyPageTower.cycleInfinity (E.homologyPageTower pq)

/-- The eventual boundary subobject `B_infinity^{pq}`. -/
@[stacks 011O]
noncomputable abbrev boundaryInfinity (E : SpectralSequence C c 1) (pq : κ)
    : Subobject E⟦1, pq⟧ :=
  HomologyPageTower.boundaryInfinity (E.homologyPageTower pq)

namespace InfinityPage

/-- Eventual boundaries are contained in eventual cycles. -/
@[stacks 011O]
theorem boundary_le_cycle (E : SpectralSequence C c 1) (pq : κ) :
    E.boundaryInfinity pq ≤ E.cycleInfinity pq := sorry

end InfinityPage

/-- The infinity-page entry `Z_infinity^{pq} / B_infinity^{pq}`. -/
@[stacks 011O]
noncomputable abbrev infinityPage (E : SpectralSequence C c 1) (pq : κ) : C :=
  HomologyPageTower.infinityPage (E.homologyPageTower pq)

namespace InfinityPage

/-- The canonical projection from eventual cycles to the proof-free infinity-page entry. -/
@[stacks 011O]
noncomputable abbrev π (E : SpectralSequence C c 1) (pq : κ) :
    (E.cycleInfinity pq : C) ⟶ E.infinityPage pq :=
  HomologyPageTower.InfinityPage.π (E.homologyPageTower pq)

/-- The proof-free infinity-page entry is isomorphic to the textbook quotient once eventual
boundary containment is available. -/
@[stacks 011O]
theorem isIsomorphic (E : SpectralSequence C c 1) (pq : κ) :
    IsIsomorphic (E.infinityPage pq)
      (cokernel
        (Subobject.ofLE (E.boundaryInfinity pq) (E.cycleInfinity pq)
          (boundary_le_cycle E pq))) := sorry

end InfinityPage

end Infinity

/-- A spectral sequence degenerates at `E_r` when every differential on page `r` and later
pages vanishes. -/
@[stacks 011O]
def degeneratesAt (E : SpectralSequence C c 1) (r : ℕ+) : Prop :=
  ∀ (pq : κ) (s : ℕ+), r ≤ s → (E.positivePage s).dFrom pq = 0

/-- Degeneration persists after increasing the page index. -/
theorem degeneratesAt_mono (E : SpectralSequence C c 1) {r s : ℕ+} (hrs : r ≤ s) :
    E.degeneratesAt r → E.degeneratesAt s := sorry

end SpectralSequence
end CategoryTheory
