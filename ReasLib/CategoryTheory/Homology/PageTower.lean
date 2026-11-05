/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Abelian.Subobject
public import Mathlib.CategoryTheory.Subobject.Lattice
public import Mathlib.Data.PNat.Order
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Homology.ShortComplex.Cycles
public import ReasLib.CategoryTheory.Subobject.Quotient.Intersection

/-!
# Towers of Successive Homology Pages

A `HomologyPageTower` records page objects in an abelian category, the cycle and boundary
subobjects on each page, and the canonical quotient comparison with the next page.  The module
constructs once and for all the induced cycle and boundary filtrations inside the first page.
This owner applies equally to graded entries of ordinary spectral sequences and to ungraded
spectral sequences whose differential is shifted by an autoequivalence.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe v u

namespace CategoryTheory

variable (C : Type u) [Category.{v} C] [Abelian C]

/-- A tower in which every next page is the quotient of the current page cycles by its
boundaries.  The comparison map is retained explicitly, since it is the map used by recursive
cycle and boundary constructions. -/
@[stacks 011O, stacks 0AMI]
structure HomologyPageTower where
  /-- The object on positive page `r`. -/
  page (r : ℕ+) : C
  /-- The cycle subobject on page `r`. -/
  pageCycle (r : ℕ+) : Subobject (page r)
  /-- The boundary subobject on page `r`. -/
  pageBoundary (r : ℕ+) : Subobject (page r)
  /-- Page boundaries are contained in page cycles. -/
  pageBoundary_le_pageCycle (r : ℕ+) : pageBoundary r ≤ pageCycle r
  /-- The canonical map from page cycles to the next page. -/
  toNext (r : ℕ+) : (pageCycle r : C) ⟶ page (r + 1)
  /-- The page-boundary inclusion is killed by the map to the next page. -/
  pageBoundary_toNext_zero (r : ℕ+) :
    Subobject.ofLE (pageBoundary r) (pageCycle r) (pageBoundary_le_pageCycle r) ≫
      toNext r = 0
  /-- The map induced from the page quotient to the next page is an isomorphism. -/
  isIso_descToNext (r : ℕ+) :
    IsIso
      (cokernel.desc
        (Subobject.ofLE (pageBoundary r) (pageCycle r) (pageBoundary_le_pageCycle r))
        (toNext r) (pageBoundary_toNext_zero r))

namespace HomologyPageTower

variable {C : Type u} [Category.{v} C] [Abelian C]

/-! ## Homology on one page -/

/-- The homology of page `r`, namely its cycles modulo its boundaries. -/
@[stacks 011O, stacks 0AMI "page homology"]
noncomputable def pageHomology (P : HomologyPageTower C) (r : ℕ+) : C :=
  cokernel
    (Subobject.ofLE (P.pageBoundary r) (P.pageCycle r)
      (P.pageBoundary_le_pageCycle r))

/-- The projection from page cycles to page homology. -/
@[stacks 011O, stacks 0AMI "page homology projection"]
noncomputable abbrev pageHomologyπ (P : HomologyPageTower C) (r : ℕ+) :
    (P.pageCycle r : C) ⟶ P.pageHomology r :=
  cokernel.π
    (Subobject.ofLE (P.pageBoundary r) (P.pageCycle r)
      (P.pageBoundary_le_pageCycle r))

namespace PageHomology

/-- The canonical comparison from the homology quotient on page `r` to page `r + 1`. -/
@[stacks 011O, stacks 0AMI "page homology comparison"]
noncomputable def toNext (P : HomologyPageTower C) (r : ℕ+) :
    P.pageHomology r ⟶ P.page (r + 1) :=
  cokernel.desc _ (P.toNext r) (P.pageBoundary_toNext_zero r)

/-- The local homology quotient is canonically isomorphic to the next page. -/
instance toNext_isIso (P : HomologyPageTower C) (r : ℕ+) :
    IsIso (toNext P r) :=
  P.isIso_descToNext r

/-- The projection to local homology followed by the next-page comparison is `toNext`. -/
@[reassoc (attr := simp)]
theorem π_toNext (P : HomologyPageTower C) (r : ℕ+) :
    P.pageHomologyπ r ≫ toNext P r = P.toNext r := by
  exact cokernel.π_desc _ _ _

end PageHomology

/-! ## Recursive cycle and boundary stages -/

/-- The positive page index `n + 1` corresponding to a zero-based recursive stage. -/
abbrev pageIndex (n : ℕ) : ℕ+ :=
  Nat.succPNat n

/-- A recursive cycle stage inside the first page, together with its canonical map to the
corresponding page object. -/
@[stacks 011O, stacks 0AMI "recursive cycle stage"]
structure CycleStage (P : HomologyPageTower C) (n : ℕ) where
  /-- The cycle subobject `Z_{n+1} ≤ P.page 1`. -/
  cycle : Subobject (P.page 1)
  /-- The canonical epimorphism `Z_{n+1} ⟶ P.page (n+1)`. -/
  toPage : (cycle : C) ⟶ P.page (pageIndex n)

namespace CycleStage

/-- Pull the current page cycles back to a recursive cycle stage. -/
def pulledCycles {P : HomologyPageTower C} {n : ℕ} (stage : CycleStage P n) :
    Subobject (stage.cycle : C) :=
  (Subobject.pullback stage.toPage).obj (P.pageCycle (pageIndex n))

/-- Regard the pulled-back cycles as a subobject of the ambient first page, using the canonical
composite-arrow representative. -/
def nextCycle {P : HomologyPageTower C} {n : ℕ} (stage : CycleStage P n) :
    Subobject (P.page 1) :=
  Subobject.mk (stage.pulledCycles.arrow ≫ stage.cycle.arrow)

/-- The canonical composite-arrow representative agrees with mapping the pulled-back cycles
along the current cycle inclusion. -/
theorem nextCycle_eq_map {P : HomologyPageTower C} {n : ℕ} (stage : CycleStage P n) :
    stage.nextCycle = (Subobject.map stage.cycle.arrow).obj stage.pulledCycles := by
  simpa only [nextCycle, Subobject.map_mk] using
    congrArg (Subobject.map stage.cycle.arrow).obj (Subobject.mk_arrow stage.pulledCycles)

/-- The canonical map from the next recursive cycle stage to the next page object. -/
noncomputable def nextToPage {P : HomologyPageTower C} {n : ℕ} (stage : CycleStage P n) :
    (stage.nextCycle : C) ⟶ P.page (pageIndex (n + 1)) :=
  (Subobject.underlyingIso (stage.pulledCycles.arrow ≫ stage.cycle.arrow)).hom ≫
    Subobject.pullbackπ stage.toPage (P.pageCycle (pageIndex n)) ≫
      P.toNext (pageIndex n)

/-- Advance a recursive cycle stage by one page. -/
noncomputable def next {P : HomologyPageTower C} {n : ℕ}
    (stage : CycleStage P n) : CycleStage P (n + 1) where
  cycle := stage.nextCycle
  toPage := stage.nextToPage

/-- Pull the current page boundaries back to a recursive cycle stage. -/
def pulledBoundaries {P : HomologyPageTower C} {n : ℕ} (stage : CycleStage P n) :
    Subobject (stage.cycle : C) :=
  (Subobject.pullback stage.toPage).obj (P.pageBoundary (pageIndex n))

/-- Map the pulled-back boundaries into the ambient first page. -/
def nextBoundary {P : HomologyPageTower C} {n : ℕ} (stage : CycleStage P n) :
    Subobject (P.page 1) :=
  (Subobject.map stage.cycle.arrow).obj stage.pulledBoundaries

end CycleStage

/-- The recursively constructed cycle stages inside the first page. -/
@[stacks 011O, stacks 0AMI "recursive cycle-stage construction"]
noncomputable def cycleStage (P : HomologyPageTower C) : (n : ℕ) → CycleStage P n
  | 0 =>
      { cycle := ⊤
        toPage := (⊤ : Subobject (P.page 1)).arrow }
  | n + 1 => (P.cycleStage n).next

/-- The zero-based recursive boundary stages inside the first page. -/
@[stacks 011O, stacks 0AMI "recursive boundary-stage construction"]
noncomputable def boundaryStage (P : HomologyPageTower C) : ℕ → Subobject (P.page 1)
  | 0 => ⊥
  | n + 1 => (P.cycleStage n).nextBoundary

/-- The cycle subobject `Z_r` inside the first page of a homology page tower. -/
@[stacks 011O, stacks 0AMI]
abbrev cycle (P : HomologyPageTower C) (r : ℕ+) : Subobject (P.page 1) :=
  (P.cycleStage r.natPred).cycle

/-- The boundary subobject `B_r` inside the first page of a homology page tower. -/
@[stacks 011O, stacks 0AMI]
abbrev boundary (P : HomologyPageTower C) (r : ℕ+) : Subobject (P.page 1) :=
  P.boundaryStage r.natPred

/-- The first cycle subobject is the top subobject. -/
theorem cycle_one (P : HomologyPageTower C) : P.cycle 1 = ⊤ := by
  rfl

/-- The first boundary subobject is the bottom subobject. -/
theorem boundary_one (P : HomologyPageTower C) : P.boundary 1 = ⊥ := by
  rfl

/-- Every recursive boundary stage is contained in the corresponding cycle stage. -/
theorem boundary_le_cycle (P : HomologyPageTower C) (r : ℕ+) :
    P.boundary r ≤ P.cycle r := by
  change P.boundaryStage r.natPred ≤ (P.cycleStage r.natPred).cycle
  cases h : r.natPred with
  | zero => exact bot_le
  | succ n =>
      change (P.cycleStage n).nextBoundary ≤ (P.cycleStage n).nextCycle
      rw [CycleStage.nextCycle_eq_map]
      exact (Subobject.map _).monotone
        ((Subobject.pullback _).monotone (P.pageBoundary_le_pageCycle _))

/-! ## Pullback to a homology presentation -/

/-- The zero-based cycle filtration on a short-complex presentation of the first page of a
homology page tower. -/
@[stacks 0AMK, stacks 011Z "predecessor cycle filtration"]
noncomputable def preimageCycle (P : HomologyPageTower C) (S : ShortComplex C) [S.HasHomology]
    (e : P.page 1 ≅ S.homology) : ℕ → Subobject S.X₂
  | 0 => ⊤
  | n + 1 => ShortComplex.Cycles.preimageOfIso S e (P.cycle (pageIndex n))

/-- The zero-based boundary filtration on a short-complex presentation of the first page of a
homology page tower. -/
@[stacks 0AMK, stacks 011Z "predecessor boundary filtration"]
noncomputable def preimageBoundary (P : HomologyPageTower C) (S : ShortComplex C) [S.HasHomology]
    (e : P.page 1 ≅ S.homology) : ℕ → Subobject S.X₂
  | 0 => ⊥
  | n + 1 => ShortComplex.Cycles.preimageOfIso S e (P.boundary (pageIndex n))

/-- The initial pulled-back cycle stage is the whole middle object. -/
@[simp]
theorem preimageCycle_zero (P : HomologyPageTower C) (S : ShortComplex C) [S.HasHomology]
    (e : P.page 1 ≅ S.homology) :
    P.preimageCycle S e 0 = ⊤ := by
  rfl

/-- A positive pulled-back cycle stage is the preimage of the corresponding recursive cycle
stage on the first page. -/
@[simp]
theorem preimageCycle_succ (P : HomologyPageTower C) (S : ShortComplex C) [S.HasHomology]
    (e : P.page 1 ≅ S.homology) (n : ℕ) :
    P.preimageCycle S e (n + 1) =
      ShortComplex.Cycles.preimageOfIso S e (P.cycle (pageIndex n)) := by
  rfl

/-- The initial pulled-back boundary stage is zero. -/
@[simp]
theorem preimageBoundary_zero (P : HomologyPageTower C) (S : ShortComplex C) [S.HasHomology]
    (e : P.page 1 ≅ S.homology) :
    P.preimageBoundary S e 0 = ⊥ := by
  rfl

/-- A positive pulled-back boundary stage is the preimage of the corresponding recursive
boundary stage on the first page. -/
@[simp]
theorem preimageBoundary_succ (P : HomologyPageTower C) (S : ShortComplex C) [S.HasHomology]
    (e : P.page 1 ≅ S.homology) (n : ℕ) :
    P.preimageBoundary S e (n + 1) =
      ShortComplex.Cycles.preimageOfIso S e (P.boundary (pageIndex n)) := by
  rfl

/-- The canonical map from `Z_r` to page `r`. -/
@[stacks 011O, stacks 0AMI "recursive cycle-to-page map"]
noncomputable def cycleToPage (P : HomologyPageTower C) (r : ℕ+) :
    (P.cycle r : C) ⟶ P.page r :=
  (P.cycleStage r.natPred).toPage ≫
    (eqToIso (congrArg P.page (PNat.succPNat_natPred r))).hom

namespace Cycle

/-- The canonical map to page `r` from any subobject identified with the recursive cycle stage.
The identifying equality is explicit because it changes the source object of the morphism. -/
@[stacks 011O, stacks 0AMI "cycle-to-page map from an equal presentation"]
noncomputable def toPageOf (P : HomologyPageTower C) (r : ℕ+)
    {Z : Subobject (P.page 1)} (hZ : P.cycle r = Z) :
    (Z : C) ⟶ P.page r :=
  (Subobject.isoOfEq _ _ hZ.symm).hom ≫ P.cycleToPage r

/-- The map from an equal presentation of a recursive cycle stage is independent of the equality
witness. -/
@[stacks 011O, stacks 0AMI "cycle-to-page proof irrelevance"]
theorem toPageOf_proof_irrel (P : HomologyPageTower C) (r : ℕ+)
    {Z : Subobject (P.page 1)} (hZ hZ' : P.cycle r = Z) :
    toPageOf P r hZ = toPageOf P r hZ' := by
  rfl

/-- A map from a presentation `Z` of the recursive cycle stage to page `r` is canonical when it
is the map `toPageOf` for some explicit identification `P.cycle r = Z`. -/
@[stacks 011O, stacks 0AMI "cycle-to-page map specification"]
def IsToPageOf (P : HomologyPageTower C) (r : ℕ+) (Z : Subobject (P.page 1))
    (q : (Z : C) ⟶ P.page r) : Prop :=
  ∃ hZ : P.cycle r = Z, q = toPageOf P r hZ

/-- The canonical map from an explicitly identified cycle presentation satisfies
`IsToPageOf`. -/
@[stacks 011O, stacks 0AMI "canonical cycle-to-page map specification"]
theorem toPageOf_isToPageOf (P : HomologyPageTower C) (r : ℕ+)
    {Z : Subobject (P.page 1)} (hZ : P.cycle r = Z) :
    IsToPageOf P r Z (toPageOf P r hZ) := by
  exact ⟨hZ, rfl⟩

namespace IsToPageOf

/-- Two maps satisfying the canonical cycle-to-page specification are equal. -/
@[stacks 011O, stacks 0AMI "cycle-to-page map uniqueness"]
theorem unique {P : HomologyPageTower C} {r : ℕ+} {Z : Subobject (P.page 1)}
    {q q' : (Z : C) ⟶ P.page r}
    (hq : IsToPageOf P r Z q) (hq' : IsToPageOf P r Z q') :
    q = q' := by
  obtain ⟨hZ, rfl⟩ := hq
  obtain ⟨hZ', rfl⟩ := hq'
  rfl

end IsToPageOf

/-- The cycle-to-page map from the recursive cycle stage itself is the canonical cycle-to-page
map. -/
@[simp, stacks 011O, stacks 0AMI "cycle-to-page self presentation"]
theorem toPageOf_self (P : HomologyPageTower C) (r : ℕ+) :
    toPageOf P r rfl = P.cycleToPage r := by
  simp [toPageOf, Subobject.isoOfEq]

/-- On the first page, `cycleToPage` is the cycle inclusion. -/
theorem toPage_one (P : HomologyPageTower C) :
    P.cycleToPage 1 = (P.cycle 1).arrow := by
  change (⊤ : Subobject (P.page 1)).arrow ≫ 𝟙 _ = _
  exact Category.comp_id _

/-- The successor cycle is the pullback of the current page cycles, mapped into page one. -/
theorem succ_eq_pullback (P : HomologyPageTower C) (r : ℕ+) :
    P.cycle (r + 1) =
      (Subobject.map (P.cycle r).arrow).obj
        ((Subobject.pullback (P.cycleToPage r)).obj (P.pageCycle r)) := by
  obtain ⟨n, rfl⟩ := Equiv.pnatEquivNat.symm.surjective r
  change P.cycle (pageIndex (n + 1)) =
    (Subobject.map (P.cycle (pageIndex n)).arrow).obj
      ((Subobject.pullback (P.cycleToPage (pageIndex n))).obj (P.pageCycle (pageIndex n)))
  simpa only [cycle, cycleToPage, pageIndex, Nat.natPred_succPNat,
    eqToIso_refl, Iso.refl_hom, Category.comp_id, cycleStage, CycleStage.next,
    CycleStage.pulledCycles] using (P.cycleStage n).nextCycle_eq_map

/-- The canonical map from `Z_r` to page `r` is an epimorphism. -/
instance toPage_epi (P : HomologyPageTower C) (r : ℕ+) :
    Epi (P.cycleToPage r) := by
  have h (n : ℕ) : Epi (P.cycleStage n).toPage := by
    induction n with
    | zero =>
        change Epi (⊤ : Subobject (P.page 1)).arrow
        infer_instance
    | succ n ih =>
        haveI := ih
        haveI : Epi (P.toNext (pageIndex n)) := by
          haveI : Epi (P.pageHomologyπ (pageIndex n)) :=
            inferInstanceAs (Epi (cokernel.π _))
          haveI := PageHomology.toNext_isIso P (pageIndex n)
          rw [← PageHomology.π_toNext P (pageIndex n)]
          infer_instance
        haveI : Epi (Subobject.pullbackπ (P.cycleStage n).toPage
            (P.pageCycle (pageIndex n))) :=
          Abelian.epi_fst_of_isLimit _ _ (Subobject.isPullback _ _).isLimit
        change Epi (P.cycleStage n).nextToPage
        dsimp only [CycleStage.nextToPage]
        exact epi_comp' (inferInstanceAs (Epi (Subobject.underlyingIso _).hom))
          (epi_comp' ‹Epi (Subobject.pullbackπ (P.cycleStage n).toPage
            (P.pageCycle (pageIndex n)))› ‹Epi (P.toNext (pageIndex n))›)
  haveI := h r.natPred
  dsimp only [cycleToPage]
  infer_instance

end Cycle

/-! The kernel characterization below follows directly from the local quotient and the
recursive pullback construction. -/

omit [Abelian C] in
private theorem mapFactors {X Y A : C} (i : X ⟶ Y) [Mono i]
    (S : Subobject X) (f : A ⟶ X) :
    ((Subobject.map i).obj S).Factors (f ≫ i) ↔ S.Factors f := by
  have hm : (Subobject.map i).obj S = Subobject.mk (S.arrow ≫ i) := by
    calc
      _ = (Subobject.map i).obj (Subobject.mk S.arrow) :=
        congrArg (Subobject.map i).obj (Subobject.mk_arrow S).symm
      _ = _ := Subobject.map_mk _ _
  rw [hm, Subobject.mk_factors_iff, Subobject.factors_iff S f]
  change (∃ g : A ⟶ (S : C), g ≫ (S.arrow ≫ i) = f ≫ i) ↔
    ∃ g : A ⟶ (S : C), g ≫ S.arrow = f
  simp only [← Category.assoc, cancel_mono i]

set_option backward.isDefEq.respectTransparency false in
private theorem pageToNext_zero_iff (P : HomologyPageTower C) (r : ℕ+)
    {A : C} (f : A ⟶ (P.pageCycle r : C)) :
    f ≫ P.toNext r = 0 ↔ (P.pageBoundary r).Factors (f ≫ (P.pageCycle r).arrow) := by
  let i := Subobject.ofLE (P.pageBoundary r) (P.pageCycle r) (P.pageBoundary_le_pageCycle r)
  have hker := Abelian.monoIsKernelOfCokernel _ (cokernelIsCokernel i)
  haveI := PageHomology.toNext_isIso P r
  constructor
  · intro hf
    have hπ : f ≫ P.pageHomologyπ r = 0 := by
      apply (cancel_mono (PageHomology.toNext P r)).mp
      simpa only [Category.assoc, PageHomology.π_toNext, zero_comp] using hf
    obtain ⟨l, hl⟩ := KernelFork.IsLimit.lift' hker f hπ
    change l ≫ i = f at hl
    apply (Subobject.factors_iff _ _).mpr
    refine ⟨l, ?_⟩
    change l ≫ (P.pageBoundary r).arrow = f ≫ (P.pageCycle r).arrow
    rw [← hl]
    simp [i, Category.assoc]
  · intro hf
    obtain ⟨l, hl⟩ := (Subobject.factors_iff _ _).mp hf
    change l ≫ (P.pageBoundary r).arrow = f ≫ (P.pageCycle r).arrow at hl
    have hi : l ≫ i = f := by
      apply (cancel_mono (P.pageCycle r).arrow).mp
      simpa only [i, Category.assoc, Subobject.ofLE_arrow] using hl
    rw [← hi]
    simp only [i, Category.assoc, P.pageBoundary_toNext_zero, comp_zero]

set_option backward.isDefEq.respectTransparency false in
private theorem nextToPage_zero_iff {P : HomologyPageTower C} {n : ℕ}
    (stage : CycleStage P n) {A : C} (f : A ⟶ (stage.nextCycle : C)) :
    f ≫ stage.nextToPage = 0 ↔ stage.nextBoundary.Factors (f ≫ stage.nextCycle.arrow) := by
  let e := Subobject.underlyingIso (stage.pulledCycles.arrow ≫ stage.cycle.arrow)
  have hArrow : f ≫ stage.nextCycle.arrow =
      ((f ≫ e.hom) ≫ stage.pulledCycles.arrow) ≫ stage.cycle.arrow := by
    simp [e, Category.assoc, CycleStage.nextCycle]
  calc
    _ ↔ (P.pageBoundary (pageIndex n)).Factors
        (((f ≫ e.hom) ≫ Subobject.pullbackπ stage.toPage (P.pageCycle (pageIndex n))) ≫
          (P.pageCycle (pageIndex n)).arrow) := by
      simpa only [CycleStage.nextToPage, e, Category.assoc] using
        pageToNext_zero_iff P (pageIndex n)
          ((f ≫ e.hom) ≫ Subobject.pullbackπ stage.toPage (P.pageCycle (pageIndex n)))
    _ ↔ stage.pulledBoundaries.Factors ((f ≫ e.hom) ≫ stage.pulledCycles.arrow) := by
      rw [CycleStage.pulledBoundaries, pullback_factors_iff]
      change (P.pageBoundary (pageIndex n)).Factors
          (((f ≫ e.hom) ≫ Subobject.pullbackπ stage.toPage (P.pageCycle (pageIndex n))) ≫
            (P.pageCycle (pageIndex n)).arrow) ↔
        (P.pageBoundary (pageIndex n)).Factors
          (((f ≫ e.hom) ≫ ((Subobject.pullback stage.toPage).obj
            (P.pageCycle (pageIndex n))).arrow) ≫ stage.toPage)
      rw [Category.assoc, (Subobject.isPullback stage.toPage
        (P.pageCycle (pageIndex n))).w, ← Category.assoc]
    _ ↔ _ := by
      rw [hArrow]
      exact (mapFactors stage.cycle.arrow stage.pulledBoundaries
        ((f ≫ e.hom) ≫ stage.pulledCycles.arrow)).symm

private theorem stageToPage_zero_iff (P : HomologyPageTower C) (n : ℕ)
    {A : C} (f : A ⟶ ((P.cycleStage n).cycle : C)) :
    f ≫ (P.cycleStage n).toPage = 0 ↔
      (P.boundaryStage n).Factors (f ≫ (P.cycleStage n).cycle.arrow) := by
  cases n with
  | zero =>
      change f ≫ (⊤ : Subobject (P.page 1)).arrow = 0 ↔
        (⊥ : Subobject (P.page 1)).Factors (f ≫ (⊤ : Subobject (P.page 1)).arrow)
      exact (Subobject.bot_factors_iff_zero _).symm
  | succ n => exact nextToPage_zero_iff (P.cycleStage n) f

set_option backward.isDefEq.respectTransparency false in
private theorem cycleToPage_zero_iff (P : HomologyPageTower C) (r : ℕ+)
    {A : C} (f : A ⟶ (P.cycle r : C)) :
    f ≫ P.cycleToPage r = 0 ↔ (P.boundary r).Factors (f ≫ (P.cycle r).arrow) := by
  obtain ⟨n, rfl⟩ := Equiv.pnatEquivNat.symm.surjective r
  change f ≫ ((P.cycleStage n).toPage ≫ 𝟙 _) = 0 ↔
    (P.boundaryStage n).Factors (f ≫ (P.cycleStage n).cycle.arrow)
  simpa only [Category.comp_id] using stageToPage_zero_iff P n f

namespace Boundary

/-- The successor boundary is the pullback of the current page boundaries, mapped into page one. -/
theorem succ_eq_pullback (P : HomologyPageTower C) (r : ℕ+) :
    P.boundary (r + 1) =
      (Subobject.map (P.cycle r).arrow).obj
        ((Subobject.pullback (P.cycleToPage r)).obj (P.pageBoundary r)) := by
  obtain ⟨n, rfl⟩ := Equiv.pnatEquivNat.symm.surjective r
  change P.boundary (pageIndex (n + 1)) =
    (Subobject.map (P.cycle (pageIndex n)).arrow).obj
      ((Subobject.pullback (P.cycleToPage (pageIndex n))).obj (P.pageBoundary (pageIndex n)))
  simp only [boundary, cycle, cycleToPage, pageIndex, Nat.natPred_succPNat,
    eqToIso_refl, Iso.refl_hom, Category.comp_id]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The map from `Z_r` to page `r` kills the included boundary subobject `B_r`. -/
theorem toPage_zero (P : HomologyPageTower C) (r : ℕ+) :
    Subobject.ofLE (P.boundary r) (P.cycle r) (P.boundary_le_cycle r) ≫
      P.cycleToPage r = 0 := by
  apply (cycleToPage_zero_iff P r _).mpr
  simpa only [Subobject.ofLE_arrow] using Subobject.factors_self (P.boundary r)

/-- The map from `Z_r` to page `r` kills the intersection of the boundary and cycle stages.
This is the proof shape required by the proof-free intersection-quotient representative. -/
@[stacks 011O, stacks 0AMI "recursive intersection quotient vanishing"]
theorem intersection_toPage_zero (P : HomologyPageTower C) (r : ℕ+) :
    Subobject.ofLE (P.boundary r ⊓ P.cycle r) (P.cycle r) _root_.inf_le_right ≫
      P.cycleToPage r = 0 := by
  rw [← Subobject.ofLE_comp_ofLE (P.boundary r ⊓ P.cycle r) (P.boundary r)
    (P.cycle r) inf_le_left (P.boundary_le_cycle r), Category.assoc,
    toPage_zero, comp_zero]

end Boundary

namespace CycleStage

/-- Every recursive stage map is an epimorphism. -/
instance toPage_epi (P : HomologyPageTower C) (n : ℕ) :
    Epi (P.cycleStage n).toPage := by
  have h := Cycle.toPage_epi P (pageIndex n)
  change Epi ((P.cycleStage n).toPage ≫ 𝟙 _) at h
  simpa only [Category.comp_id] using h

end CycleStage

/-! ## Recursive page quotients -/

/-- The proof-free recursive page quotient `Z_r / (B_r ⊓ Z_r)`.  The intrinsic containment
theorem identifies it with the textbook quotient `Z_r / B_r` without making its concrete carrier
depend on deferred proof data. -/
@[stacks 011O, stacks 0AMI "recursive page quotient"]
noncomputable def pageQuotient (P : HomologyPageTower C) (r : ℕ+) : C :=
  Subobject.intersectionQuotient (P.boundary r) (P.cycle r)

/-- The canonical projection from `Z_r` to the proof-free recursive page quotient. -/
@[stacks 011O, stacks 0AMI "recursive page quotient projection"]
noncomputable abbrev pageQuotientπ (P : HomologyPageTower C) (r : ℕ+) :
    (P.cycle r : C) ⟶ P.pageQuotient r :=
  Subobject.IntersectionQuotient.π (P.boundary r) (P.cycle r)

namespace PageQuotient

/-- The map from the proof-free page quotient to page `r` induced by `cycleToPage`.  Its
explicit vanishing witness keeps this concrete map independent of deferred filtration proofs. -/
@[stacks 011O, stacks 0AMI "recursive page quotient comparison"]
noncomputable def toPage (P : HomologyPageTower C) (r : ℕ+)
    (h_zero : Subobject.ofLE (P.boundary r ⊓ P.cycle r) (P.cycle r) _root_.inf_le_right ≫
      P.cycleToPage r = 0) :
    P.pageQuotient r ⟶ P.page r :=
  Subobject.IntersectionQuotient.desc (P.boundary r) (P.cycle r) (P.cycleToPage r) h_zero

/-- The recursive page-quotient comparison is independent of the proof that its boundary-cycle
intersection vanishes. -/
@[stacks 011O, stacks 0AMI "recursive page quotient comparison proof irrelevance"]
theorem toPage_proof_irrel (P : HomologyPageTower C) (r : ℕ+)
    (h_zero h_zero' : Subobject.ofLE (P.boundary r ⊓ P.cycle r) (P.cycle r)
      _root_.inf_le_right ≫ P.cycleToPage r = 0) :
    toPage P r h_zero = toPage P r h_zero' := by
  rfl

/-- The quotient projection followed by its comparison to page `r` is `cycleToPage`. -/
@[reassoc (attr := simp)]
theorem π_toPage (P : HomologyPageTower C) (r : ℕ+)
    (h_zero : Subobject.ofLE (P.boundary r ⊓ P.cycle r) (P.cycle r) _root_.inf_le_right ≫
      P.cycleToPage r = 0) :
    P.pageQuotientπ r ≫ toPage P r h_zero = P.cycleToPage r := by
  exact cokernel.π_desc _ _ _

/-- A map from the recursive page quotient to page `r` is canonical when precomposition with
the quotient projection recovers the cycle-to-page map.  This property keeps downstream
statements independent of the vanishing witness required to construct `toPage`. -/
@[stacks 011O, stacks 0AMI "recursive page quotient comparison specification"]
def IsToPage (P : HomologyPageTower C) (r : ℕ+)
    (q : P.pageQuotient r ⟶ P.page r) : Prop :=
  P.pageQuotientπ r ≫ q = P.cycleToPage r

/-- The descended recursive page-quotient comparison satisfies its intrinsic specification. -/
@[stacks 011O, stacks 0AMI "canonical recursive page quotient comparison specification"]
theorem toPage_isToPage (P : HomologyPageTower C) (r : ℕ+)
    (h_zero : Subobject.ofLE (P.boundary r ⊓ P.cycle r) (P.cycle r) _root_.inf_le_right ≫
      P.cycleToPage r = 0) :
    IsToPage P r (toPage P r h_zero) := by
  exact π_toPage P r h_zero

namespace IsToPage

/-- Two maps from a recursive page quotient satisfying the canonical comparison specification
are equal. -/
@[stacks 011O, stacks 0AMI "uniqueness of recursive page quotient comparison"]
theorem unique {P : HomologyPageTower C} {r : ℕ+}
    {q q' : P.pageQuotient r ⟶ P.page r}
    (hq : IsToPage P r q) (hq' : IsToPage P r q') :
    q = q' := by
  apply coequalizer.hom_ext
  exact hq.trans hq'.symm

end IsToPage

set_option backward.isDefEq.respectTransparency false in
/-- The literal quotient comparison to page `r` is an isomorphism. -/
@[stacks 011O, stacks 0AMI "recursive page quotient isomorphism"]
theorem toPage_isIso (P : HomologyPageTower C) (r : ℕ+)
    (h_zero : Subobject.ofLE (P.boundary r ⊓ P.cycle r) (P.cycle r) _root_.inf_le_right ≫
      P.cycleToPage r = 0) :
    IsIso (toPage P r h_zero) := by
  let i := Subobject.ofLE (P.boundary r ⊓ P.cycle r) (P.cycle r) inf_le_right
  have hker : IsLimit (KernelFork.ofι i h_zero) := by
    apply KernelFork.IsLimit.ofι'
    intro A f hf
    have hb := (cycleToPage_zero_iff P r f).mp hf
    have hInf : (P.boundary r ⊓ P.cycle r).Factors (f ≫ (P.cycle r).arrow) := by
      rw [inf_eq_left.mpr (P.boundary_le_cycle r)]
      exact hb
    refine ⟨(P.boundary r ⊓ P.cycle r).factorThru _ hInf, ?_⟩
    apply (cancel_mono (P.cycle r).arrow).mp
    simp [i, Category.assoc]
  have hcol := Abelian.epiIsCokernelOfKernel _ hker
  let e := IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel i) hcol
  have he : PageQuotient.toPage P r h_zero = e.hom := by
    apply coequalizer.hom_ext
    change cokernel.π i ≫ PageQuotient.toPage P r h_zero = cokernel.π i ≫ e.hom
    rw [PageQuotient.π_toPage]
    exact (IsColimit.comp_coconePointUniqueUpToIso_hom (cokernelIsCokernel i)
      hcol WalkingParallelPair.one).symm
  rw [he]
  infer_instance

/-- The proof-free recursive page quotient is isomorphic to the literal textbook quotient
`Z_r / B_r`. -/
@[stacks 011O, stacks 0AMI "recursive page quotient cokernel comparison"]
theorem isIsomorphicCokernel (P : HomologyPageTower C) (r : ℕ+) :
    IsIsomorphic (P.pageQuotient r)
      (cokernel
        (Subobject.ofLE (P.boundary r) (P.cycle r) (P.boundary_le_cycle r))) := by
  refine ⟨cokernel.mapIso _ _
    (Subobject.isoOfEq _ _ (inf_eq_left.mpr (P.boundary_le_cycle r)))
    (Iso.refl _) ?_⟩
  apply (cancel_mono (P.cycle r).arrow).mp
  simp [Subobject.isoOfEq]

/-- The recursive page quotient is isomorphic to page `r`. -/
@[stacks 011O, stacks 0AMI "recursive page quotient presentation"]
theorem isIsomorphic (P : HomologyPageTower C) (r : ℕ+) :
    IsIsomorphic (P.pageQuotient r) (P.page r) := by
  let h := Boundary.intersection_toPage_zero P r
  letI := toPage_isIso P r h
  exact ⟨asIso (toPage P r h)⟩

/-- Package an explicitly supplied isomorphism witness for the literal page quotient. -/
@[stacks 011O, stacks 0AMI "recursive page quotient iso"]
noncomputable def isoOf (P : HomologyPageTower C) (r : ℕ+)
    (h_zero : Subobject.ofLE (P.boundary r ⊓ P.cycle r) (P.cycle r) _root_.inf_le_right ≫
      P.cycleToPage r = 0)
    (h_iso : IsIso (toPage P r h_zero)) :
    P.pageQuotient r ≅ P.page r :=
  @asIso C _ _ _ (toPage P r h_zero) h_iso

/-- The canonical identification of the recursive quotient with its page.  The vanishing
and invertibility proofs are supplied by the recursive construction. -/
@[stacks 011O, stacks 0AMI "canonical recursive page quotient iso"]
noncomputable def pageIso (P : HomologyPageTower C) (r : ℕ+) :
    P.pageQuotient r ≅ P.page r :=
  isoOf P r (Boundary.intersection_toPage_zero P r)
    (toPage_isIso P r (Boundary.intersection_toPage_zero P r))

/-- The canonical quotient identification recovers the specified map on cycles. -/
@[reassoc (attr := simp)]
theorem π_pageIso (P : HomologyPageTower C) (r : ℕ+) :
    P.pageQuotientπ r ≫ (pageIso P r).hom = P.cycleToPage r := by
  exact π_toPage P r (Boundary.intersection_toPage_zero P r)

end PageQuotient

/-! ## Filtration order -/

namespace Cycle

/-- Successor cycle subobjects form a descending chain. -/
theorem succ_le (P : HomologyPageTower C) (r : ℕ+) :
    P.cycle (r + 1) ≤ P.cycle r := by
  rw [succ_eq_pullback]
  calc
    _ ≤ (Subobject.map (P.cycle r).arrow).obj ⊤ := (Subobject.map _).monotone le_top
    _ = P.cycle r := by rw [Subobject.map_top, Subobject.mk_arrow]

/-- The cycle filtration is antitone in the page index. -/
theorem antitone (P : HomologyPageTower C) :
    ∀ ⦃r s : ℕ+⦄, r ≤ s → P.cycle s ≤ P.cycle r := by
  intro r s hrs
  have h : Antitone (fun n : ℕ => P.cycle (pageIndex n)) :=
    antitone_nat_of_succ_le (fun n => succ_le P (pageIndex n))
  simpa only [pageIndex, PNat.succPNat_natPred] using h (PNat.natPred_monotone hrs)

end Cycle

namespace Boundary

set_option backward.isDefEq.respectTransparency false in
/-- Successor boundary subobjects form an ascending chain. -/
theorem le_succ (P : HomologyPageTower C) (r : ℕ+) :
    P.boundary r ≤ P.boundary (r + 1) := by
  rw [Boundary.succ_eq_pullback]
  apply Subobject.le_of_factors
  let i := Subobject.ofLE (P.boundary r) (P.cycle r) (P.boundary_le_cycle r)
  have h0 : i ≫ P.cycleToPage r = 0 := toPage_zero P r
  have hf : ((Subobject.pullback (P.cycleToPage r)).obj (P.pageBoundary r)).Factors i :=
    pullback_factors _ _ i (by rw [h0]; exact Subobject.factors_zero)
  have hm := (mapFactors (P.cycle r).arrow _ i).mpr hf
  simpa only [i, Subobject.ofLE_arrow] using hm

/-- The boundary filtration is monotone in the page index. -/
theorem monotone (P : HomologyPageTower C) :
    ∀ ⦃r s : ℕ+⦄, r ≤ s → P.boundary r ≤ P.boundary s := by
  intro r s hrs
  have h : Monotone (fun n : ℕ => P.boundary (pageIndex n)) :=
    monotone_nat_of_le_succ (fun n => le_succ P (pageIndex n))
  simpa only [pageIndex, PNat.succPNat_natPred] using h (PNat.natPred_monotone hrs)

/-- Every boundary stage is contained in every cycle stage. -/
theorem le_cycle (P : HomologyPageTower C) (r s : ℕ+) :
    P.boundary r ≤ P.cycle s := by
  rcases le_total r s with hrs | hsr
  · exact (monotone P hrs).trans (P.boundary_le_cycle s)
  · exact (P.boundary_le_cycle r).trans (Cycle.antitone P hsr)

end Boundary

/-! ## Morphisms and induced quotient maps -/

/-- A morphism of homology page towers is a pagewise map preserving page cycles and boundaries
and commuting with the canonical maps to the next page.  Preservation is recorded as a
factorization property, so the restricted maps remain canonical. -/
@[ext, stacks 011O, stacks 0AMI "homology-page tower morphism"]
structure Hom (P Q : HomologyPageTower C) where
  /-- The morphism between the objects on page `r`. -/
  app (r : ℕ+) : P.page r ⟶ Q.page r
  /-- The pagewise map factors through the cycle subobject. -/
  pageCycle_factors (r : ℕ+) :
    (Q.pageCycle r).Factors ((P.pageCycle r).arrow ≫ app r)
  /-- The pagewise map factors through the boundary subobject. -/
  pageBoundary_factors (r : ℕ+) :
    (Q.pageBoundary r).Factors ((P.pageBoundary r).arrow ≫ app r)
  /-- The restricted map on page cycles commutes with passage to the next page. -/
  toNext_comm (r : ℕ+) :
    (Q.pageCycle r).factorThru
        ((P.pageCycle r).arrow ≫ app r) (pageCycle_factors r) ≫ Q.toNext r =
      P.toNext r ≫ app (r + 1)
  /-- The restricted page-boundary and page-cycle maps commute with the boundary inclusion. -/
  pageBoundary_map_comp_ofLE (r : ℕ+) :
    Subobject.ofLE (P.pageBoundary r) (P.pageCycle r) (P.pageBoundary_le_pageCycle r) ≫
        (Q.pageCycle r).factorThru
          ((P.pageCycle r).arrow ≫ app r) (pageCycle_factors r) =
      (Q.pageBoundary r).factorThru
          ((P.pageBoundary r).arrow ≫ app r) (pageBoundary_factors r) ≫
        Subobject.ofLE (Q.pageBoundary r) (Q.pageCycle r) (Q.pageBoundary_le_pageCycle r)
  /-- The first-page component factors through the recursive cycle stage. -/
  cycle_factors (r : ℕ+) :
    (Q.cycle r).Factors ((P.cycle r).arrow ≫ app 1)
  /-- The first-page component factors through the recursive boundary stage. -/
  boundary_factors (r : ℕ+) :
    (Q.boundary r).Factors ((P.boundary r).arrow ≫ app 1)
  /-- The recursively restricted boundary and cycle maps commute with `B_r ↪ Z_r`. -/
  boundary_map_comp_ofLE (r : ℕ+) :
    Subobject.ofLE (P.boundary r) (P.cycle r) (P.boundary_le_cycle r) ≫
        (Q.cycle r).factorThru ((P.cycle r).arrow ≫ app 1) (cycle_factors r) =
      (Q.boundary r).factorThru ((P.boundary r).arrow ≫ app 1) (boundary_factors r) ≫
        Subobject.ofLE (Q.boundary r) (Q.cycle r) (Q.boundary_le_cycle r)
  /-- The first-page component factors through the recursive boundary-cycle intersection. -/
  intersection_factors (r : ℕ+) :
    (Q.boundary r ⊓ Q.cycle r).Factors
      ((P.boundary r ⊓ P.cycle r).arrow ≫ app 1)
  /-- The restricted recursive intersection and cycle maps commute with the inclusion into the
  cycle stage. -/
  intersection_map_comp_ofLE (r : ℕ+) :
    Subobject.ofLE (P.boundary r ⊓ P.cycle r) (P.cycle r) _root_.inf_le_right ≫
        (Q.cycle r).factorThru ((P.cycle r).arrow ≫ app 1) (cycle_factors r) =
      (Q.boundary r ⊓ Q.cycle r).factorThru
          ((P.boundary r ⊓ P.cycle r).arrow ≫ app 1) (intersection_factors r) ≫
        Subobject.ofLE (Q.boundary r ⊓ Q.cycle r) (Q.cycle r) _root_.inf_le_right

namespace Hom

set_option backward.isDefEq.respectTransparency false in
private theorem lift_cycleStage {P Q : HomologyPageTower C}
    (app : ∀ r : ℕ+, P.page r ⟶ Q.page r)
    (hC : ∀ r : ℕ+, (Q.pageCycle r).Factors ((P.pageCycle r).arrow ≫ app r))
    (hnext : ∀ r : ℕ+,
      (Q.pageCycle r).factorThru ((P.pageCycle r).arrow ≫ app r) (hC r) ≫ Q.toNext r =
        P.toNext r ≫ app (r + 1)) (n : ℕ) :
    ∃ g : ((P.cycleStage n).cycle : C) ⟶ ((Q.cycleStage n).cycle : C),
      g ≫ (Q.cycleStage n).cycle.arrow = (P.cycleStage n).cycle.arrow ≫ app 1 ∧
      g ≫ (Q.cycleStage n).toPage = (P.cycleStage n).toPage ≫ app (pageIndex n) := by
  induction n with
  | zero =>
      refine ⟨(⊤ : Subobject (P.page 1)).arrow ≫ app 1 ≫
        inv (⊤ : Subobject (Q.page 1)).arrow, ?_, ?_⟩ <;>
        simp [cycleStage, pageIndex, Category.assoc] <;> rfl
  | succ n ih =>
      obtain ⟨g, hg, hcomm⟩ := ih
      let S := P.cycleStage n
      let T := Q.cycleStage n
      let eP := Subobject.underlyingIso (S.pulledCycles.arrow ≫ S.cycle.arrow)
      let eQ := Subobject.underlyingIso (T.pulledCycles.arrow ≫ T.cycle.arrow)
      let c := (Q.pageCycle (pageIndex n)).factorThru
        ((P.pageCycle (pageIndex n)).arrow ≫ app (pageIndex n)) (hC _)
      let a := eP.hom ≫ Subobject.pullbackπ S.toPage (P.pageCycle (pageIndex n)) ≫ c
      let b := eP.hom ≫ S.pulledCycles.arrow ≫ g
      have hw : a ≫ (Q.pageCycle (pageIndex n)).arrow = b ≫ T.toPage := by
        dsimp [a, b, c]
        simp only [Category.assoc, Subobject.factorThru_arrow]
        rw [hcomm]
        have hp : Subobject.pullbackπ S.toPage (P.pageCycle (pageIndex n)) ≫
            (P.pageCycle (pageIndex n)).arrow = S.pulledCycles.arrow ≫ S.toPage :=
          (Subobject.isPullback S.toPage (P.pageCycle (pageIndex n))).w
        simpa only [Category.assoc] using
          congrArg (fun k => eP.hom ≫ k ≫ app (pageIndex n)) hp
      let l := (Subobject.isPullback T.toPage (Q.pageCycle (pageIndex n))).lift a b hw
      have hl_snd : l ≫ T.pulledCycles.arrow = b :=
        (Subobject.isPullback T.toPage (Q.pageCycle (pageIndex n))).lift_snd a b hw
      have hl_fst : l ≫ Subobject.pullbackπ T.toPage (Q.pageCycle (pageIndex n)) = a :=
        (Subobject.isPullback T.toPage (Q.pageCycle (pageIndex n))).lift_fst a b hw
      refine ⟨l ≫ eQ.inv, ?_, ?_⟩
      · change (l ≫ eQ.inv) ≫ T.nextCycle.arrow = S.nextCycle.arrow ≫ app 1
        have he : eQ.inv ≫ T.nextCycle.arrow = T.pulledCycles.arrow ≫ T.cycle.arrow := by
          simp [eQ, CycleStage.nextCycle]
        rw [Category.assoc, he, ← Category.assoc, hl_snd]
        have hg' : g ≫ T.cycle.arrow = S.cycle.arrow ≫ app 1 := hg
        dsimp only [b]
        simp only [Category.assoc, hg']
        have heP : eP.hom ≫ (S.pulledCycles.arrow ≫ S.cycle.arrow) = S.nextCycle.arrow :=
          Subobject.underlyingIso_hom_comp_eq_mk _
        simpa only [Category.assoc] using congrArg (fun k => k ≫ app 1) heP
      · change (l ≫ eQ.inv) ≫ T.nextToPage = S.nextToPage ≫ app (pageIndex (n + 1))
        change (l ≫ eQ.inv) ≫ (eQ.hom ≫
            Subobject.pullbackπ T.toPage (Q.pageCycle (pageIndex n)) ≫ Q.toNext (pageIndex n)) =
          (eP.hom ≫ Subobject.pullbackπ S.toPage (P.pageCycle (pageIndex n)) ≫
            P.toNext (pageIndex n)) ≫ app (pageIndex (n + 1))
        simp only [Category.assoc, Iso.inv_hom_id_assoc]
        rw [← Category.assoc l, hl_fst]
        dsimp only [a, c]
        simp only [Category.assoc]
        convert congrArg (fun k => eP.hom ≫
          Subobject.pullbackπ S.toPage (P.pageCycle (pageIndex n)) ≫ k)
          (hnext (pageIndex n)) using 1 <;> rfl

/-- Compatible page maps preserve the recursively constructed cycles. -/
theorem pageMaps_cycle_factors {P Q : HomologyPageTower C}
    (app : ∀ r : ℕ+, P.page r ⟶ Q.page r)
    (hC : ∀ r : ℕ+, (Q.pageCycle r).Factors ((P.pageCycle r).arrow ≫ app r))
    (hnext : ∀ r : ℕ+,
      (Q.pageCycle r).factorThru ((P.pageCycle r).arrow ≫ app r) (hC r) ≫ Q.toNext r =
        P.toNext r ≫ app (r + 1)) (r : ℕ+) :
    (Q.cycle r).Factors ((P.cycle r).arrow ≫ app 1) := by
  obtain ⟨g, hg, _⟩ := lift_cycleStage app hC hnext r.natPred
  exact (Subobject.factors_iff _ _).mpr ⟨g, hg⟩

/-- Compatible page maps preserve the recursively constructed boundaries, the kernels of the
maps from recursive cycle stages to pages. -/
theorem pageMaps_boundary_factors {P Q : HomologyPageTower C}
    (app : ∀ r : ℕ+, P.page r ⟶ Q.page r)
    (hC : ∀ r : ℕ+, (Q.pageCycle r).Factors ((P.pageCycle r).arrow ≫ app r))
    (hnext : ∀ r : ℕ+,
      (Q.pageCycle r).factorThru ((P.pageCycle r).arrow ≫ app r) (hC r) ≫ Q.toNext r =
        P.toNext r ≫ app (r + 1)) (r : ℕ+) :
    (Q.boundary r).Factors ((P.boundary r).arrow ≫ app 1) := by
  obtain ⟨g, hg, hcomm⟩ := lift_cycleStage app hC hnext r.natPred
  let i := Subobject.ofLE (P.boundary r) (P.cycle r) (P.boundary_le_cycle r)
  have hi : i ≫ (P.cycleStage r.natPred).toPage = 0 :=
    (stageToPage_zero_iff P r.natPred i).mpr (by
      simpa only [i, Subobject.ofLE_arrow] using Subobject.factors_self (P.boundary r))
  have hz : (i ≫ g) ≫ (Q.cycleStage r.natPred).toPage = 0 := by
    rw [Category.assoc, hcomm, ← Category.assoc, hi, zero_comp]
  have hb := (stageToPage_zero_iff Q r.natPred (i ≫ g)).mp hz
  simpa only [Category.assoc, hg, i, Subobject.ofLE_arrow_assoc] using hb

/-- Construct a tower morphism from the pagewise maps and their local compatibility.  All
recursive filtration laws and inclusion squares follow from these inputs. -/
noncomputable def ofPageMaps {P Q : HomologyPageTower C}
    (app : ∀ r : ℕ+, P.page r ⟶ Q.page r)
    (hC : ∀ r : ℕ+, (Q.pageCycle r).Factors ((P.pageCycle r).arrow ≫ app r))
    (hB : ∀ r : ℕ+, (Q.pageBoundary r).Factors ((P.pageBoundary r).arrow ≫ app r))
    (hnext : ∀ r : ℕ+,
      (Q.pageCycle r).factorThru ((P.pageCycle r).arrow ≫ app r) (hC r) ≫ Q.toNext r =
        P.toNext r ≫ app (r + 1)) : Hom P Q where
  app := app
  pageCycle_factors := hC
  pageBoundary_factors := hB
  toNext_comm := hnext
  pageBoundary_map_comp_ofLE r := by
    apply (cancel_mono (Q.pageCycle r).arrow).mp
    simp [Category.assoc]
  cycle_factors := pageMaps_cycle_factors app hC hnext
  boundary_factors := pageMaps_boundary_factors app hC hnext
  boundary_map_comp_ofLE r := by
    apply (cancel_mono (Q.cycle r).arrow).mp
    simp [Category.assoc]
  intersection_factors r := by
    rw [inf_eq_left.mpr (Q.boundary_le_cycle r)]
    simpa only [Subobject.ofLE_arrow_assoc] using
      Subobject.factors_of_factors_right
        (Subobject.ofLE (P.boundary r ⊓ P.cycle r) (P.boundary r) inf_le_left)
        (pageMaps_boundary_factors app hC hnext r)
  intersection_map_comp_ofLE r := by
    apply (cancel_mono (Q.cycle r).arrow).mp
    simp [Category.assoc]

/-- The small constructor retains exactly the supplied page components. -/
@[simp]
theorem ofPageMaps_app {P Q : HomologyPageTower C}
    (app : ∀ r : ℕ+, P.page r ⟶ Q.page r)
    (hC : ∀ r : ℕ+, (Q.pageCycle r).Factors ((P.pageCycle r).arrow ≫ app r))
    (hB : ∀ r : ℕ+, (Q.pageBoundary r).Factors ((P.pageBoundary r).arrow ≫ app r))
    (hnext : ∀ r : ℕ+,
      (Q.pageCycle r).factorThru ((P.pageCycle r).arrow ≫ app r) (hC r) ≫ Q.toNext r =
        P.toNext r ≫ app (r + 1)) (r : ℕ+) :
    (ofPageMaps app hC hB hnext).app r = app r := rfl

/-- Compatible page components determine a unique tower morphism. -/
theorem existsUnique_ofPageMaps {P Q : HomologyPageTower C}
    (app : ∀ r : ℕ+, P.page r ⟶ Q.page r)
    (hC : ∀ r : ℕ+, (Q.pageCycle r).Factors ((P.pageCycle r).arrow ≫ app r))
    (hB : ∀ r : ℕ+, (Q.pageBoundary r).Factors ((P.pageBoundary r).arrow ≫ app r))
    (hnext : ∀ r : ℕ+,
      (Q.pageCycle r).factorThru ((P.pageCycle r).arrow ≫ app r) (hC r) ≫ Q.toNext r =
        P.toNext r ≫ app (r + 1)) :
    ∃! f : Hom P Q, ∀ r : ℕ+, f.app r = app r := by
  refine ⟨ofPageMaps app hC hB hnext, fun _ => rfl, ?_⟩
  intro f hf
  ext r
  exact hf r

/-- The identity page map factors through the page cycles. -/
theorem id_pageCycle_factors (P : HomologyPageTower C) (r : ℕ+) :
    (P.pageCycle r).Factors ((P.pageCycle r).arrow ≫ 𝟙 (P.page r)) := by
  simpa using Subobject.factors_self (P.pageCycle r)

/-- The identity page map factors through the page boundaries. -/
theorem id_pageBoundary_factors (P : HomologyPageTower C) (r : ℕ+) :
    (P.pageBoundary r).Factors ((P.pageBoundary r).arrow ≫ 𝟙 (P.page r)) := by
  simpa using Subobject.factors_self (P.pageBoundary r)

/-- The restricted identity on cycles commutes with passage to the next page. -/
theorem id_toNext_comm (P : HomologyPageTower C) (r : ℕ+) :
    (P.pageCycle r).factorThru
        ((P.pageCycle r).arrow ≫ 𝟙 (P.page r)) (id_pageCycle_factors P r) ≫ P.toNext r =
      P.toNext r ≫ 𝟙 (P.page (r + 1)) := by
  simp

/-- The restricted identity maps on boundaries and cycles commute with the boundary inclusion. -/
theorem id_pageBoundary_map_comp_ofLE (P : HomologyPageTower C) (r : ℕ+) :
    Subobject.ofLE (P.pageBoundary r) (P.pageCycle r) (P.pageBoundary_le_pageCycle r) ≫
        (P.pageCycle r).factorThru
          ((P.pageCycle r).arrow ≫ 𝟙 (P.page r)) (id_pageCycle_factors P r) =
      (P.pageBoundary r).factorThru
          ((P.pageBoundary r).arrow ≫ 𝟙 (P.page r)) (id_pageBoundary_factors P r) ≫
        Subobject.ofLE (P.pageBoundary r) (P.pageCycle r) (P.pageBoundary_le_pageCycle r) := by
  simp

/-- The first-page identity factors through every recursive cycle stage. -/
theorem id_cycle_factors (P : HomologyPageTower C) (r : ℕ+) :
    (P.cycle r).Factors ((P.cycle r).arrow ≫ 𝟙 (P.page 1)) := by
  simpa using Subobject.factors_self (P.cycle r)

/-- The first-page identity factors through every recursive boundary stage. -/
theorem id_boundary_factors (P : HomologyPageTower C) (r : ℕ+) :
    (P.boundary r).Factors ((P.boundary r).arrow ≫ 𝟙 (P.page 1)) := by
  simpa using Subobject.factors_self (P.boundary r)

/-- The restricted identity maps on recursive boundaries and cycles commute with `B_r ↪ Z_r`. -/
theorem id_boundary_map_comp_ofLE (P : HomologyPageTower C) (r : ℕ+) :
    Subobject.ofLE (P.boundary r) (P.cycle r) (P.boundary_le_cycle r) ≫
        (P.cycle r).factorThru
          ((P.cycle r).arrow ≫ 𝟙 (P.page 1)) (id_cycle_factors P r) =
      (P.boundary r).factorThru
          ((P.boundary r).arrow ≫ 𝟙 (P.page 1)) (id_boundary_factors P r) ≫
        Subobject.ofLE (P.boundary r) (P.cycle r) (P.boundary_le_cycle r) := by
  simp

/-- The first-page identity factors through every recursive boundary-cycle intersection. -/
theorem id_intersection_factors (P : HomologyPageTower C) (r : ℕ+) :
    (P.boundary r ⊓ P.cycle r).Factors
      ((P.boundary r ⊓ P.cycle r).arrow ≫ 𝟙 (P.page 1)) := by
  simpa using Subobject.factors_self (P.boundary r ⊓ P.cycle r)

/-- The restricted identity maps on recursive intersections and cycles commute with inclusion
into the cycle stage. -/
theorem id_intersection_map_comp_ofLE (P : HomologyPageTower C) (r : ℕ+) :
    Subobject.ofLE (P.boundary r ⊓ P.cycle r) (P.cycle r) _root_.inf_le_right ≫
        (P.cycle r).factorThru
          ((P.cycle r).arrow ≫ 𝟙 (P.page 1)) (id_cycle_factors P r) =
      (P.boundary r ⊓ P.cycle r).factorThru
          ((P.boundary r ⊓ P.cycle r).arrow ≫ 𝟙 (P.page 1))
          (id_intersection_factors P r) ≫
        Subobject.ofLE (P.boundary r ⊓ P.cycle r) (P.cycle r) _root_.inf_le_right := by
  simp

/-- The identity morphism of a homology page tower. -/
noncomputable def id (P : HomologyPageTower C) : Hom P P where
  app r := 𝟙 (P.page r)
  pageCycle_factors r := id_pageCycle_factors P r
  pageBoundary_factors r := id_pageBoundary_factors P r
  toNext_comm r := id_toNext_comm P r
  pageBoundary_map_comp_ofLE r := id_pageBoundary_map_comp_ofLE P r
  cycle_factors r := id_cycle_factors P r
  boundary_factors r := id_boundary_factors P r
  boundary_map_comp_ofLE r := id_boundary_map_comp_ofLE P r
  intersection_factors r := id_intersection_factors P r
  intersection_map_comp_ofLE r := id_intersection_map_comp_ofLE P r

/-- A composite page map factors through the target page cycles. -/
theorem comp_pageCycle_factors {P Q R : HomologyPageTower C}
    (f : Hom P Q) (g : Hom Q R) (r : ℕ+) :
    (R.pageCycle r).Factors ((P.pageCycle r).arrow ≫ (f.app r ≫ g.app r)) := by
  apply (Subobject.factors_iff _ _).mpr
  refine ⟨(Q.pageCycle r).factorThru ((P.pageCycle r).arrow ≫ f.app r) (f.pageCycle_factors r) ≫
    (R.pageCycle r).factorThru ((Q.pageCycle r).arrow ≫ g.app r) (g.pageCycle_factors r), ?_⟩
  simp [Category.assoc]

/-- A composite page map factors through the target page boundaries. -/
theorem comp_pageBoundary_factors {P Q R : HomologyPageTower C}
    (f : Hom P Q) (g : Hom Q R) (r : ℕ+) :
    (R.pageBoundary r).Factors ((P.pageBoundary r).arrow ≫ (f.app r ≫ g.app r)) := by
  apply (Subobject.factors_iff _ _).mpr
  refine ⟨(Q.pageBoundary r).factorThru ((P.pageBoundary r).arrow ≫ f.app r) (f.pageBoundary_factors r) ≫
    (R.pageBoundary r).factorThru ((Q.pageBoundary r).arrow ≫ g.app r) (g.pageBoundary_factors r), ?_⟩
  simp [Category.assoc]

/-- The restricted composite on cycles commutes with passage to the next page. -/
theorem comp_toNext_comm {P Q R : HomologyPageTower C}
    (f : Hom P Q) (g : Hom Q R) (r : ℕ+) :
    (R.pageCycle r).factorThru
        ((P.pageCycle r).arrow ≫ (f.app r ≫ g.app r))
          (comp_pageCycle_factors f g r) ≫ R.toNext r =
      P.toNext r ≫ (f.app (r + 1) ≫ g.app (r + 1)) := by
  have h : (R.pageCycle r).factorThru
      ((P.pageCycle r).arrow ≫ (f.app r ≫ g.app r))
      (comp_pageCycle_factors f g r) =
      (Q.pageCycle r).factorThru ((P.pageCycle r).arrow ≫ f.app r)
        (f.pageCycle_factors r) ≫
      (R.pageCycle r).factorThru ((Q.pageCycle r).arrow ≫ g.app r)
        (g.pageCycle_factors r) := by
    apply (cancel_mono (R.pageCycle r).arrow).mp
    simp [Category.assoc]
  rw [h, Category.assoc, g.toNext_comm, ← Category.assoc, f.toNext_comm,
    Category.assoc]

/-- The restricted composite maps on boundaries and cycles commute with the boundary inclusion. -/
theorem comp_pageBoundary_map_comp_ofLE {P Q R : HomologyPageTower C}
    (f : Hom P Q) (g : Hom Q R) (r : ℕ+) :
    Subobject.ofLE (P.pageBoundary r) (P.pageCycle r) (P.pageBoundary_le_pageCycle r) ≫
        (R.pageCycle r).factorThru
          ((P.pageCycle r).arrow ≫ (f.app r ≫ g.app r))
          (comp_pageCycle_factors f g r) =
      (R.pageBoundary r).factorThru
          ((P.pageBoundary r).arrow ≫ (f.app r ≫ g.app r))
          (comp_pageBoundary_factors f g r) ≫
        Subobject.ofLE (R.pageBoundary r) (R.pageCycle r) (R.pageBoundary_le_pageCycle r) := by
  apply (cancel_mono (R.pageCycle r).arrow).mp
  simp [Category.assoc]

/-- The composite first-page map factors through the target recursive cycle stage. -/
theorem comp_cycle_factors {P Q R : HomologyPageTower C}
    (f : Hom P Q) (g : Hom Q R) (r : ℕ+) :
    (R.cycle r).Factors ((P.cycle r).arrow ≫ (f.app 1 ≫ g.app 1)) := by
  apply (Subobject.factors_iff _ _).mpr
  refine ⟨(Q.cycle r).factorThru ((P.cycle r).arrow ≫ f.app 1) (f.cycle_factors r) ≫
    (R.cycle r).factorThru ((Q.cycle r).arrow ≫ g.app 1) (g.cycle_factors r), ?_⟩
  simp [Category.assoc]

/-- The composite first-page map factors through the target recursive boundary stage. -/
theorem comp_boundary_factors {P Q R : HomologyPageTower C}
    (f : Hom P Q) (g : Hom Q R) (r : ℕ+) :
    (R.boundary r).Factors ((P.boundary r).arrow ≫ (f.app 1 ≫ g.app 1)) := by
  apply (Subobject.factors_iff _ _).mpr
  refine ⟨(Q.boundary r).factorThru ((P.boundary r).arrow ≫ f.app 1) (f.boundary_factors r) ≫
    (R.boundary r).factorThru ((Q.boundary r).arrow ≫ g.app 1) (g.boundary_factors r), ?_⟩
  simp [Category.assoc]

/-- The recursively restricted composite maps commute with the boundary inclusion. -/
theorem comp_boundary_map_comp_ofLE {P Q R : HomologyPageTower C}
    (f : Hom P Q) (g : Hom Q R) (r : ℕ+) :
    Subobject.ofLE (P.boundary r) (P.cycle r) (P.boundary_le_cycle r) ≫
        (R.cycle r).factorThru
          ((P.cycle r).arrow ≫ (f.app 1 ≫ g.app 1))
          (comp_cycle_factors f g r) =
      (R.boundary r).factorThru
          ((P.boundary r).arrow ≫ (f.app 1 ≫ g.app 1))
          (comp_boundary_factors f g r) ≫
        Subobject.ofLE (R.boundary r) (R.cycle r) (R.boundary_le_cycle r) := by
  apply (cancel_mono (R.cycle r).arrow).mp
  simp [Category.assoc]

/-- The composite first-page map factors through the target recursive boundary-cycle
intersection. -/
theorem comp_intersection_factors {P Q R : HomologyPageTower C}
    (f : Hom P Q) (g : Hom Q R) (r : ℕ+) :
    (R.boundary r ⊓ R.cycle r).Factors
      ((P.boundary r ⊓ P.cycle r).arrow ≫ (f.app 1 ≫ g.app 1)) := by
  apply (Subobject.factors_iff _ _).mpr
  refine ⟨(Q.boundary r ⊓ Q.cycle r).factorThru ((P.boundary r ⊓ P.cycle r).arrow ≫ f.app 1) (f.intersection_factors r) ≫
    (R.boundary r ⊓ R.cycle r).factorThru ((Q.boundary r ⊓ Q.cycle r).arrow ≫ g.app 1) (g.intersection_factors r), ?_⟩
  simp [Category.assoc]

/-- The recursively restricted composite intersection and cycle maps commute with inclusion into
the cycle stage. -/
theorem comp_intersection_map_comp_ofLE {P Q R : HomologyPageTower C}
    (f : Hom P Q) (g : Hom Q R) (r : ℕ+) :
    Subobject.ofLE (P.boundary r ⊓ P.cycle r) (P.cycle r) _root_.inf_le_right ≫
        (R.cycle r).factorThru
          ((P.cycle r).arrow ≫ (f.app 1 ≫ g.app 1))
          (comp_cycle_factors f g r) =
      (R.boundary r ⊓ R.cycle r).factorThru
          ((P.boundary r ⊓ P.cycle r).arrow ≫ (f.app 1 ≫ g.app 1))
          (comp_intersection_factors f g r) ≫
        Subobject.ofLE (R.boundary r ⊓ R.cycle r) (R.cycle r) _root_.inf_le_right := by
  apply (cancel_mono (R.cycle r).arrow).mp
  simp [Category.assoc]

/-- Composition of morphisms of homology page towers. -/
noncomputable def comp {P Q R : HomologyPageTower C} (f : Hom P Q) (g : Hom Q R) :
    Hom P R where
  app r := f.app r ≫ g.app r
  pageCycle_factors r := comp_pageCycle_factors f g r
  pageBoundary_factors r := comp_pageBoundary_factors f g r
  toNext_comm r := comp_toNext_comm f g r
  pageBoundary_map_comp_ofLE r := comp_pageBoundary_map_comp_ofLE f g r
  cycle_factors r := comp_cycle_factors f g r
  boundary_factors r := comp_boundary_factors f g r
  boundary_map_comp_ofLE r := comp_boundary_map_comp_ofLE f g r
  intersection_factors r := comp_intersection_factors f g r
  intersection_map_comp_ofLE r := comp_intersection_map_comp_ofLE f g r

/-- Left identity for morphisms of homology page towers. -/
theorem id_comp {P Q : HomologyPageTower C} (f : Hom P Q) :
    comp (id P) f = f := by
  ext r
  exact Category.id_comp _

/-- Right identity for morphisms of homology page towers. -/
theorem comp_id {P Q : HomologyPageTower C} (f : Hom P Q) :
    comp f (id Q) = f := by
  ext r
  exact Category.comp_id _

/-- Associativity of morphisms of homology page towers. -/
theorem assoc {P Q R S : HomologyPageTower C}
    (f : Hom P Q) (g : Hom Q R) (h : Hom R S) :
    comp (comp f g) h = comp f (comp g h) := by
  ext r
  exact Category.assoc _ _ _

end Hom

/-- Homology page towers and their pagewise compatible morphisms form a category. -/
noncomputable instance : Category (HomologyPageTower C) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp := Hom.id_comp
  comp_id := Hom.comp_id
  assoc := Hom.assoc

/-- Evaluation of an identity tower morphism on a page. -/
@[simp]
theorem id_app (P : HomologyPageTower C) (r : ℕ+) :
    (𝟙 P : P ⟶ P).app r = 𝟙 (P.page r) := by
  rfl

/-- Evaluation of a composite tower morphism on a page. -/
@[simp]
theorem comp_app {P Q R : HomologyPageTower C} (f : P ⟶ Q) (g : Q ⟶ R) (r : ℕ+) :
    (f ≫ g).app r = f.app r ≫ g.app r := by
  rfl

namespace PageCycle

/-- Restrict an explicit page map to the cycle subobjects, using a supplied factorization. -/
@[stacks 011O, stacks 0AMI "page-cycle map with explicit factorization"]
noncomputable def mapOf {P Q : HomologyPageTower C} {r : ℕ+}
    (f : P.page r ⟶ Q.page r)
    (h_factors : (Q.pageCycle r).Factors ((P.pageCycle r).arrow ≫ f)) :
    (P.pageCycle r : C) ⟶ (Q.pageCycle r : C) :=
  (Q.pageCycle r).factorThru
    ((P.pageCycle r).arrow ≫ f) h_factors

/-- The explicitly restricted page-cycle map recovers the ambient pagewise map. -/
@[reassoc (attr := simp)]
theorem mapOf_arrow {P Q : HomologyPageTower C} {r : ℕ+}
    (f : P.page r ⟶ Q.page r)
    (h_factors : (Q.pageCycle r).Factors ((P.pageCycle r).arrow ≫ f)) :
    mapOf f h_factors ≫ (Q.pageCycle r).arrow = (P.pageCycle r).arrow ≫ f := by
  exact Subobject.factorThru_arrow _ _ _

/-- Restrict a tower morphism to the cycle subobjects on page `r`. -/
@[stacks 011O, stacks 0AMI "page-cycle map"]
noncomputable def map {P Q : HomologyPageTower C} (f : P ⟶ Q) (r : ℕ+) :
    (P.pageCycle r : C) ⟶ (Q.pageCycle r : C) :=
  mapOf (f.app r) (f.pageCycle_factors r)

/-- The restricted page-cycle map recovers the ambient pagewise map. -/
@[reassoc (attr := simp)]
theorem map_arrow {P Q : HomologyPageTower C} (f : P ⟶ Q) (r : ℕ+) :
    map f r ≫ (Q.pageCycle r).arrow = (P.pageCycle r).arrow ≫ f.app r := by
  exact mapOf_arrow _ _

/-- Restricted page-cycle maps commute with passage to the next page. -/
@[reassoc]
theorem map_toNext {P Q : HomologyPageTower C} (f : P ⟶ Q) (r : ℕ+) :
    map f r ≫ Q.toNext r = P.toNext r ≫ f.app (r + 1) := by
  exact f.toNext_comm r

end PageCycle

namespace PageBoundary

/-- Restrict an explicit page map to the boundary subobjects, using a supplied factorization. -/
@[stacks 011O, stacks 0AMI "page-boundary map with explicit factorization"]
noncomputable def mapOf {P Q : HomologyPageTower C} {r : ℕ+}
    (f : P.page r ⟶ Q.page r)
    (h_factors : (Q.pageBoundary r).Factors ((P.pageBoundary r).arrow ≫ f)) :
    (P.pageBoundary r : C) ⟶ (Q.pageBoundary r : C) :=
  (Q.pageBoundary r).factorThru
    ((P.pageBoundary r).arrow ≫ f) h_factors

/-- The explicitly restricted page-boundary map recovers the ambient pagewise map. -/
@[reassoc (attr := simp)]
theorem mapOf_arrow {P Q : HomologyPageTower C} {r : ℕ+}
    (f : P.page r ⟶ Q.page r)
    (h_factors : (Q.pageBoundary r).Factors ((P.pageBoundary r).arrow ≫ f)) :
    mapOf f h_factors ≫ (Q.pageBoundary r).arrow = (P.pageBoundary r).arrow ≫ f := by
  exact Subobject.factorThru_arrow _ _ _

/-- Restrict a tower morphism to the boundary subobjects on page `r`. -/
@[stacks 011O, stacks 0AMI "page-boundary map"]
noncomputable def map {P Q : HomologyPageTower C} (f : P ⟶ Q) (r : ℕ+) :
    (P.pageBoundary r : C) ⟶ (Q.pageBoundary r : C) :=
  mapOf (f.app r) (f.pageBoundary_factors r)

/-- The restricted page-boundary map recovers the ambient pagewise map. -/
@[reassoc (attr := simp)]
theorem map_arrow {P Q : HomologyPageTower C} (f : P ⟶ Q) (r : ℕ+) :
    map f r ≫ (Q.pageBoundary r).arrow =
      (P.pageBoundary r).arrow ≫ f.app r := by
  exact mapOf_arrow _ _

/-- The maps induced on page boundaries and cycles commute with the boundary inclusion. -/
theorem map_comp_ofLE {P Q : HomologyPageTower C} (f : P ⟶ Q) (r : ℕ+) :
    Subobject.ofLE (P.pageBoundary r) (P.pageCycle r) (P.pageBoundary_le_pageCycle r) ≫
        PageCycle.map f r =
      map f r ≫
        Subobject.ofLE (Q.pageBoundary r) (Q.pageCycle r) (Q.pageBoundary_le_pageCycle r) := by
  exact f.pageBoundary_map_comp_ofLE r

end PageBoundary

section PageFunctorDef

variable (C)

/-- Evaluation at page `r` is a functor from homology page towers to the ambient category. -/
@[stacks 011O, stacks 0AMI "page evaluation functor"]
noncomputable def pageFunctor (r : ℕ+) : HomologyPageTower C ⥤ C where
  obj P := P.page r
  map f := f.app r
  map_id P := id_app P r
  map_comp f g := comp_app f g r

end PageFunctorDef

namespace PageFunctor

/-- Evaluation of the page functor on an object is the corresponding page object. -/
@[simp]
theorem obj (r : ℕ+) (P : HomologyPageTower C) :
    (pageFunctor C r).obj P = P.page r := by
  rfl

/-- Evaluation of the page functor on a morphism is its page component. -/
@[simp]
theorem map {P Q : HomologyPageTower C} (f : P ⟶ Q) (r : ℕ+) :
    (pageFunctor C r).map f = f.app r := by
  rfl

end PageFunctor

namespace PageHomology

/-- The map on a local homology quotient induced by explicit maps on page boundaries and cycles
forming the defining square.  The restricted maps are supplied as data rather than selected from
factorization proofs. -/
@[stacks 011O, stacks 0AMI "page homology map with explicit factorizations"]
noncomputable def mapOf {P Q : HomologyPageTower C} {r : ℕ+}
    (boundary : (P.pageBoundary r : C) ⟶ (Q.pageBoundary r : C))
    (cycle : (P.pageCycle r : C) ⟶ (Q.pageCycle r : C))
    (h_comm :
      Subobject.ofLE (P.pageBoundary r) (P.pageCycle r) (P.pageBoundary_le_pageCycle r) ≫
          cycle =
        boundary ≫
          Subobject.ofLE (Q.pageBoundary r) (Q.pageCycle r) (Q.pageBoundary_le_pageCycle r)) :
    P.pageHomology r ⟶ Q.pageHomology r :=
  Subobject.Quotient.map boundary cycle h_comm

/-- The explicit-square local homology map is characterized on representatives from page
cycles. -/
@[reassoc (attr := simp)]
theorem π_naturalityOf {P Q : HomologyPageTower C} {r : ℕ+}
    (boundary : (P.pageBoundary r : C) ⟶ (Q.pageBoundary r : C))
    (cycle : (P.pageCycle r : C) ⟶ (Q.pageCycle r : C))
    (h_comm :
      Subobject.ofLE (P.pageBoundary r) (P.pageCycle r) (P.pageBoundary_le_pageCycle r) ≫
          cycle =
        boundary ≫
          Subobject.ofLE (Q.pageBoundary r) (Q.pageCycle r) (Q.pageBoundary_le_pageCycle r)) :
    P.pageHomologyπ r ≫ mapOf boundary cycle h_comm = cycle ≫ Q.pageHomologyπ r := by
  exact cokernel.π_desc _ _ _

/-- The map induced on the local homology quotient of a page by a morphism of homology page
towers. -/
@[stacks 011O, stacks 0AMI "page homology map"]
noncomputable def map {P Q : HomologyPageTower C} (f : P ⟶ Q) (r : ℕ+) :
    P.pageHomology r ⟶ Q.pageHomology r :=
  mapOf (PageBoundary.map f r) (PageCycle.map f r) (f.pageBoundary_map_comp_ofLE r)

/-- The map on local homology quotients is characterized on representatives from the page
cycles. -/
@[reassoc (attr := simp)]
theorem π_naturality {P Q : HomologyPageTower C} (f : P ⟶ Q) (r : ℕ+) :
    P.pageHomologyπ r ≫ map f r = PageCycle.map f r ≫ Q.pageHomologyπ r := by
  exact π_naturalityOf _ _ _

/-- A local page-homology map is induced by a tower morphism when its composite with the
homology projection is the corresponding restricted map on page cycles. -/
@[stacks 011O, stacks 0AMI "induced page homology map"]
def IsInduced {P Q : HomologyPageTower C} (f : P ⟶ Q) (r : ℕ+)
    (q : P.pageHomology r ⟶ Q.pageHomology r) : Prop :=
  P.pageHomologyπ r ≫ q = PageCycle.map f r ≫ Q.pageHomologyπ r

/-- The canonical local page-homology map is induced by its tower morphism. -/
@[stacks 011O, stacks 0AMI "canonical induced page homology map"]
theorem map_isInduced {P Q : HomologyPageTower C} (f : P ⟶ Q) (r : ℕ+) :
    IsInduced f r (map f r) := by
  exact π_naturality f r

namespace IsInduced

/-- Two local page-homology maps induced by the same tower morphism are equal. -/
@[stacks 011O, stacks 0AMI "uniqueness of induced page homology maps"]
theorem unique {P Q : HomologyPageTower C} {f : P ⟶ Q} {r : ℕ+}
    {q q' : P.pageHomology r ⟶ Q.pageHomology r}
    (hq : IsInduced f r q) (hq' : IsInduced f r q') :
    q = q' := by
  apply coequalizer.hom_ext
  exact hq.trans hq'.symm

end IsInduced

/-- Local homology quotient maps commute with the specified comparisons to the following
page. -/
@[reassoc]
theorem toNext_naturality {P Q : HomologyPageTower C} (f : P ⟶ Q) (r : ℕ+) :
    map f r ≫ toNext Q r = toNext P r ≫ f.app (r + 1) := by
  apply coequalizer.hom_ext
  change P.pageHomologyπ r ≫ (map f r ≫ toNext Q r) =
    P.pageHomologyπ r ≫ (toNext P r ≫ f.app (r + 1))
  simp only [π_naturality_assoc, π_toNext_assoc, π_toNext,
    PageCycle.map_toNext]

/-- The local homology quotient comparison is an isomorphism onto the following page. -/
@[stacks 011O, stacks 0AMI "local homology quotient comparison"]
noncomputable def iso (P : HomologyPageTower C) (r : ℕ+) :
    P.pageHomology r ≅ P.page (r + 1) :=
  @asIso C _ _ _ (toNext P r) (toNext_isIso P r)

/-- The forward map of the local homology quotient comparison is the canonical map to the
following page. -/
theorem iso_hom (P : HomologyPageTower C) (r : ℕ+) :
    (iso P r).hom = toNext P r := by
  rfl

/-- The inverse local homology quotient comparison is the categorical inverse of the canonical
map to the following page. -/
theorem iso_inv (P : HomologyPageTower C) (r : ℕ+) :
    (iso P r).inv = inv (toNext P r) := by
  rfl

/-- The local homology quotient comparisons are natural in a tower morphism. -/
theorem iso_naturality {P Q : HomologyPageTower C} (f : P ⟶ Q) (r : ℕ+) :
    map f r ≫ (iso Q r).hom = (iso P r).hom ≫ f.app (r + 1) := by
  exact toNext_naturality f r

/-- The inverse local homology quotient comparisons are natural in a tower morphism. -/
theorem iso_inv_naturality {P Q : HomologyPageTower C} (f : P ⟶ Q) (r : ℕ+) :
    f.app (r + 1) ≫ (iso Q r).inv = (iso P r).inv ≫ map f r := by
  apply (cancel_mono (iso Q r).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [iso_naturality, Iso.inv_hom_id_assoc]

/-- Local homology quotient maps preserve identity tower morphisms. -/
@[simp]
theorem map_id (P : HomologyPageTower C) (r : ℕ+) :
    map (𝟙 P) r = 𝟙 (P.pageHomology r) := by
  apply (cancel_mono (toNext P r)).mp
  simp [toNext_naturality]

/-- Local homology quotient maps preserve composition of tower morphisms. -/
@[simp]
theorem map_comp {P Q R : HomologyPageTower C}
    (f : P ⟶ Q) (g : Q ⟶ R) (r : ℕ+) :
    map (f ≫ g) r = map f r ≫ map g r := by
  apply (cancel_mono (toNext R r)).mp
  simp only [toNext_naturality, Category.assoc, comp_app]
  rw [← Category.assoc (map f r), toNext_naturality, Category.assoc]

section Functor

variable (C)

/-- Taking the quotient of page cycles by page boundaries is functorial in homology page
towers. -/
@[stacks 011O, stacks 0AMI "page homology functor"]
noncomputable def functor (r : ℕ+) : HomologyPageTower C ⥤ C where
  obj P := P.pageHomology r
  map f := PageHomology.map f r
  map_id P := PageHomology.map_id P r
  map_comp f g := PageHomology.map_comp f g r

/-- Evaluation of the local homology quotient functor on a tower is its local quotient. -/
@[simp]
theorem Functor.obj (r : ℕ+) (P : HomologyPageTower C) :
    (functor C r).obj P = P.pageHomology r := by
  rfl

/-- Evaluation of the local homology quotient functor on a tower morphism is the induced local
quotient map. -/
@[simp]
theorem Functor.map {P Q : HomologyPageTower C} (f : P ⟶ Q) (r : ℕ+) :
    (functor C r).map f = PageHomology.map f r := by
  rfl

/-- The local homology quotient on page `r` is naturally isomorphic to evaluation on page
`r + 1`. -/
@[stacks 011O, stacks 0AMI "page homology functor comparison"]
noncomputable def Functor.iso (r : ℕ+) :
  functor C r ≅ pageFunctor C (r + 1) :=
  NatIso.ofComponents (fun P ↦ PageHomology.iso P r)
    (fun f ↦ PageHomology.iso_naturality f r)

/-- The forward component of the page-homology functor comparison is the local quotient
comparison. -/
@[simp, stacks 011O, stacks 0AMI "page homology functor comparison component"]
theorem Functor.iso_hom_app (r : ℕ+) (P : HomologyPageTower C) :
    (Functor.iso C r).hom.app P = (PageHomology.iso P r).hom := by
  rfl

/-- The inverse component of the page-homology functor comparison is the inverse local quotient
comparison. -/
@[simp, stacks 011O, stacks 0AMI "page homology functor comparison inverse component"]
theorem Functor.iso_inv_app (r : ℕ+) (P : HomologyPageTower C) :
    (Functor.iso C r).inv.app P = (PageHomology.iso P r).inv := by
  rfl

end Functor

end PageHomology

namespace Cycle

/-- A tower morphism maps recursive cycle stages into recursive cycle stages. -/
theorem map_le {P Q : HomologyPageTower C} (f : P ⟶ Q) (r : ℕ+) :
    (Subobject.exists (f.app 1)).obj (P.cycle r) ≤ Q.cycle r := by
  apply leOfHom
  refine ((Subobject.existsPullbackAdj (f.app 1)).homEquiv _ _).symm ?_
  exact homOfLE (Subobject.le_of_factors
    (pullback_factors (f.app 1) (Q.cycle r) (P.cycle r).arrow (f.cycle_factors r)))

/-- The map between recursive cycle stages induced by an explicit first-page map and a supplied
factorization. -/
@[stacks 011O, stacks 0AMI "recursive cycle map with explicit factorization"]
noncomputable def mapOf {P Q : HomologyPageTower C} {r : ℕ+}
    (f : P.page 1 ⟶ Q.page 1)
    (h_factors : (Q.cycle r).Factors ((P.cycle r).arrow ≫ f)) :
    (P.cycle r : C) ⟶ (Q.cycle r : C) :=
  (Q.cycle r).factorThru ((P.cycle r).arrow ≫ f) h_factors

/-- The explicitly restricted recursive cycle map recovers the first-page map after inclusion. -/
@[reassoc (attr := simp)]
theorem mapOf_arrow {P Q : HomologyPageTower C} {r : ℕ+}
    (f : P.page 1 ⟶ Q.page 1)
    (h_factors : (Q.cycle r).Factors ((P.cycle r).arrow ≫ f)) :
    mapOf f h_factors ≫ (Q.cycle r).arrow = (P.cycle r).arrow ≫ f := by
  exact Subobject.factorThru_arrow _ _ _

/-- The map induced between recursive cycle stages. -/
@[stacks 011O, stacks 0AMI "recursive cycle map"]
noncomputable def map {P Q : HomologyPageTower C} (f : P ⟶ Q) (r : ℕ+) :
    (P.cycle r : C) ⟶ (Q.cycle r : C) :=
  mapOf (f.app 1) (f.cycle_factors r)

/-- The recursive cycle map recovers the first-page map after inclusion. -/
@[reassoc (attr := simp)]
theorem map_arrow {P Q : HomologyPageTower C} (f : P ⟶ Q) (r : ℕ+) :
    map f r ≫ (Q.cycle r).arrow = (P.cycle r).arrow ≫ f.app 1 := by
  exact mapOf_arrow _ _

set_option backward.isDefEq.respectTransparency false in
/-- Recursive cycle maps commute with the canonical maps to page `r`. -/
@[reassoc]
theorem toPage_naturality {P Q : HomologyPageTower C} (f : P ⟶ Q) (r : ℕ+) :
    map f r ≫ Q.cycleToPage r = P.cycleToPage r ≫ f.app r := by
  obtain ⟨n, rfl⟩ := Equiv.pnatEquivNat.symm.surjective r
  change Cycle.map f (pageIndex n) ≫ Q.cycleToPage (pageIndex n) =
    P.cycleToPage (pageIndex n) ≫ f.app (pageIndex n)
  induction n with
  | zero =>
      change Cycle.map f 1 ≫ Q.cycleToPage 1 = P.cycleToPage 1 ≫ f.app 1
      rw [Cycle.toPage_one, Cycle.toPage_one, Cycle.map_arrow]
  | succ n ih =>
      let p := P.cycleStage n
      let q := Q.cycleStage n
      let eP := Subobject.underlyingIso (p.pulledCycles.arrow ≫ p.cycle.arrow)
      let eQ := Subobject.underlyingIso (q.pulledCycles.arrow ≫ q.cycle.arrow)
      let k : (p.pulledCycles : C) ⟶ (q.pulledCycles : C) :=
        eP.inv ≫ Cycle.map f (pageIndex (n + 1)) ≫ eQ.hom
      have hP : eP.inv ≫ (P.cycle (pageIndex (n + 1))).arrow =
          p.pulledCycles.arrow ≫ p.cycle.arrow := Subobject.underlyingIso_arrow _
      have hQ : eQ.hom ≫ q.pulledCycles.arrow ≫ q.cycle.arrow =
          (Q.cycle (pageIndex (n + 1))).arrow := Subobject.underlyingIso_hom_comp_eq_mk _
      have hinc : k ≫ q.pulledCycles.arrow =
          p.pulledCycles.arrow ≫ Cycle.map f (pageIndex n) := by
        apply (cancel_mono q.cycle.arrow).mp
        calc
          _ = eP.inv ≫ Cycle.map f (pageIndex (n + 1)) ≫
              (Q.cycle (pageIndex (n + 1))).arrow := by simp only [k, Category.assoc, hQ]
          _ = eP.inv ≫ (P.cycle (pageIndex (n + 1))).arrow ≫ f.app 1 := by
            rw [Cycle.map_arrow]
          _ = (p.pulledCycles.arrow ≫ p.cycle.arrow) ≫ f.app 1 := by
            rw [← Category.assoc, hP]
          _ = _ := by
            simpa only [p, q, cycle, pageIndex, Nat.natPred_succPNat, Category.assoc] using
              congrArg (p.pulledCycles.arrow ≫ ·) (Cycle.map_arrow f (pageIndex n)).symm
      have ih' : Cycle.map f (pageIndex n) ≫ q.toPage = p.toPage ≫ f.app (pageIndex n) := by
        change Cycle.map f (pageIndex n) ≫ (q.toPage ≫ 𝟙 _) =
          (p.toPage ≫ 𝟙 _) ≫ f.app (pageIndex n) at ih
        simpa only [Category.comp_id] using ih
      have hπ : k ≫ Subobject.pullbackπ q.toPage (Q.pageCycle (pageIndex n)) =
          Subobject.pullbackπ p.toPage (P.pageCycle (pageIndex n)) ≫ PageCycle.map f (pageIndex n) := by
        apply (cancel_mono (Q.pageCycle (pageIndex n)).arrow).mp
        calc
          _ = (k ≫ q.pulledCycles.arrow) ≫ q.toPage := by
            simp only [CycleStage.pulledCycles, Category.assoc,
              (Subobject.isPullback q.toPage (Q.pageCycle (pageIndex n))).w]
          _ = p.pulledCycles.arrow ≫ Cycle.map f (pageIndex n) ≫ q.toPage := by
            rw [hinc, Category.assoc]
          _ = p.pulledCycles.arrow ≫ p.toPage ≫ f.app (pageIndex n) := by rw [ih']
          _ = (Subobject.pullbackπ p.toPage (P.pageCycle (pageIndex n)) ≫
              (P.pageCycle (pageIndex n)).arrow) ≫ f.app (pageIndex n) := by
            simp only [CycleStage.pulledCycles,
              (Subobject.isPullback p.toPage (P.pageCycle (pageIndex n))).w, Category.assoc]
          _ = _ := by simp only [CycleStage.pulledCycles, Category.assoc, PageCycle.map_arrow]
      have hNextP : P.cycleToPage (pageIndex (n + 1)) =
          eP.hom ≫ Subobject.pullbackπ p.toPage (P.pageCycle (pageIndex n)) ≫ P.toNext (pageIndex n) := by
        change (P.cycleStage (n + 1)).toPage ≫ 𝟙 _ = _
        rw [Category.comp_id]
        rfl
      have hNextQ : Q.cycleToPage (pageIndex (n + 1)) =
          eQ.hom ≫ Subobject.pullbackπ q.toPage (Q.pageCycle (pageIndex n)) ≫ Q.toNext (pageIndex n) := by
        change (Q.cycleStage (n + 1)).toPage ≫ 𝟙 _ = _
        rw [Category.comp_id]
        rfl
      apply (cancel_epi eP.inv).mp
      have hn : (k ≫ Subobject.pullbackπ q.toPage (Q.pageCycle (pageIndex n))) ≫ Q.toNext (pageIndex n) =
          Subobject.pullbackπ p.toPage (P.pageCycle (pageIndex n)) ≫ P.toNext (pageIndex n) ≫
            f.app (pageIndex n + 1) := by
        rw [hπ, Category.assoc, PageCycle.map_toNext]
      calc
        _ = (k ≫ Subobject.pullbackπ q.toPage (Q.pageCycle (pageIndex n))) ≫
            Q.toNext (pageIndex n) := by
          rw [hNextQ]
          simp only [k, Category.assoc]
        _ = _ := hn
        _ = _ := by
          rw [hNextP]
          simp only [Category.assoc, Iso.inv_hom_id_assoc]
          rfl

/-- Recursive cycle maps preserve identity tower morphisms. -/
@[simp, stacks 011O, stacks 0AMI "recursive cycle-map functoriality"]
theorem map_id (P : HomologyPageTower C) (r : ℕ+) :
    map (𝟙 P) r = 𝟙 (P.cycle r : C) := by
  apply (cancel_mono (P.cycle r).arrow).mp
  simp

/-- Recursive cycle maps preserve composition of tower morphisms. -/
@[simp, stacks 011O, stacks 0AMI "recursive cycle-map functoriality"]
theorem map_comp {P Q R : HomologyPageTower C}
    (f : P ⟶ Q) (g : Q ⟶ R) (r : ℕ+) :
    map (f ≫ g) r = map f r ≫ map g r := by
  apply (cancel_mono (R.cycle r).arrow).mp
  simp [Category.assoc]

section Functor

variable (C)

/-- Taking the recursive cycle stage at page `r` is functorial in homology page towers. -/
@[stacks 011O, stacks 0AMI "recursive cycle-stage functor"]
noncomputable def functor (r : ℕ+) : HomologyPageTower C ⥤ C where
  obj P := (P.cycle r : C)
  map f := Cycle.map f r
  map_id P := Cycle.map_id P r
  map_comp f g := Cycle.map_comp f g r

/-- Evaluation of the recursive cycle-stage functor on an object is the corresponding cycle
stage. -/
@[simp]
theorem Functor.obj (r : ℕ+) (P : HomologyPageTower C) :
    (functor C r).obj P = (P.cycle r : C) := by
  rfl

/-- Evaluation of the recursive cycle-stage functor on a morphism is the induced cycle map. -/
@[simp]
theorem Functor.map {P Q : HomologyPageTower C} (f : P ⟶ Q) (r : ℕ+) :
    (functor C r).map f = Cycle.map f r := by
  rfl

end Functor

end Cycle

namespace Boundary

/-- A tower morphism maps recursive boundary stages into recursive boundary stages. -/
theorem map_le {P Q : HomologyPageTower C} (f : P ⟶ Q) (r : ℕ+) :
    (Subobject.exists (f.app 1)).obj (P.boundary r) ≤ Q.boundary r := by
  apply leOfHom
  refine ((Subobject.existsPullbackAdj (f.app 1)).homEquiv _ _).symm ?_
  exact homOfLE (Subobject.le_of_factors
    (pullback_factors (f.app 1) (Q.boundary r) (P.boundary r).arrow (f.boundary_factors r)))

/-- The map between recursive boundary stages induced by an explicit first-page map and a
supplied factorization. -/
@[stacks 011O, stacks 0AMI "recursive boundary map with explicit factorization"]
noncomputable def mapOf {P Q : HomologyPageTower C} {r : ℕ+}
    (f : P.page 1 ⟶ Q.page 1)
    (h_factors : (Q.boundary r).Factors ((P.boundary r).arrow ≫ f)) :
    (P.boundary r : C) ⟶ (Q.boundary r : C) :=
  (Q.boundary r).factorThru ((P.boundary r).arrow ≫ f) h_factors

/-- The explicitly restricted recursive boundary map recovers the first-page map after
inclusion. -/
@[reassoc (attr := simp)]
theorem mapOf_arrow {P Q : HomologyPageTower C} {r : ℕ+}
    (f : P.page 1 ⟶ Q.page 1)
    (h_factors : (Q.boundary r).Factors ((P.boundary r).arrow ≫ f)) :
    mapOf f h_factors ≫ (Q.boundary r).arrow = (P.boundary r).arrow ≫ f := by
  exact Subobject.factorThru_arrow _ _ _

/-- The map induced between recursive boundary stages. -/
@[stacks 011O, stacks 0AMI "recursive boundary map"]
noncomputable def map {P Q : HomologyPageTower C} (f : P ⟶ Q) (r : ℕ+) :
    (P.boundary r : C) ⟶ (Q.boundary r : C) :=
  mapOf (f.app 1) (f.boundary_factors r)

/-- The recursive boundary map recovers the first-page map after inclusion. -/
@[reassoc (attr := simp)]
theorem map_arrow {P Q : HomologyPageTower C} (f : P ⟶ Q) (r : ℕ+) :
    map f r ≫ (Q.boundary r).arrow =
      (P.boundary r).arrow ≫ f.app 1 := by
  exact mapOf_arrow _ _

/-- The recursive boundary and cycle maps form a commutative square. -/
theorem map_comp_ofLE {P Q : HomologyPageTower C} (f : P ⟶ Q) (r : ℕ+) :
    Subobject.ofLE (P.boundary r) (P.cycle r) (P.boundary_le_cycle r) ≫ Cycle.map f r =
      map f r ≫
        Subobject.ofLE (Q.boundary r) (Q.cycle r) (Q.boundary_le_cycle r) := by
  exact f.boundary_map_comp_ofLE r

/-- Recursive boundary maps preserve identity tower morphisms. -/
@[simp, stacks 011O, stacks 0AMI "recursive boundary-map functoriality"]
theorem map_id (P : HomologyPageTower C) (r : ℕ+) :
    map (𝟙 P) r = 𝟙 (P.boundary r : C) := by
  apply (cancel_mono (P.boundary r).arrow).mp
  simp

/-- Recursive boundary maps preserve composition of tower morphisms. -/
@[simp, stacks 011O, stacks 0AMI "recursive boundary-map functoriality"]
theorem map_comp {P Q R : HomologyPageTower C}
    (f : P ⟶ Q) (g : Q ⟶ R) (r : ℕ+) :
    map (f ≫ g) r = map f r ≫ map g r := by
  apply (cancel_mono (R.boundary r).arrow).mp
  simp [Category.assoc]

section Functor

variable (C)

/-- Taking the recursive boundary stage at page `r` is functorial in homology page towers. -/
@[stacks 011O, stacks 0AMI "recursive boundary-stage functor"]
noncomputable def functor (r : ℕ+) : HomologyPageTower C ⥤ C where
  obj P := (P.boundary r : C)
  map f := Boundary.map f r
  map_id P := Boundary.map_id P r
  map_comp f g := Boundary.map_comp f g r

/-- Evaluation of the recursive boundary-stage functor on an object is the corresponding
boundary stage. -/
@[simp]
theorem Functor.obj (r : ℕ+) (P : HomologyPageTower C) :
    (functor C r).obj P = (P.boundary r : C) := by
  rfl

/-- Evaluation of the recursive boundary-stage functor on a morphism is the induced boundary
map. -/
@[simp]
theorem Functor.map {P Q : HomologyPageTower C} (f : P ⟶ Q) (r : ℕ+) :
    (functor C r).map f = Boundary.map f r := by
  rfl

end Functor

end Boundary

namespace PageQuotient

/-- The map between recursive boundary-cycle intersections induced by an explicit first-page
map and a supplied factorization through the target intersection. -/
@[stacks 011O, stacks 0AMI "recursive boundary-cycle intersection map with an explicit factorization"]
noncomputable def intersectionMapOf {P Q : HomologyPageTower C} {r : ℕ+}
    (f : P.page 1 ⟶ Q.page 1)
    (h_factors : (Q.boundary r ⊓ Q.cycle r).Factors
      ((P.boundary r ⊓ P.cycle r).arrow ≫ f)) :
    ((P.boundary r ⊓ P.cycle r : Subobject (P.page 1)) : C) ⟶
      ((Q.boundary r ⊓ Q.cycle r : Subobject (Q.page 1)) : C) :=
  (Q.boundary r ⊓ Q.cycle r).factorThru
    ((P.boundary r ⊓ P.cycle r).arrow ≫ f) h_factors

/-- The canonical map between recursive boundary-cycle intersections induced by a tower
morphism. -/
@[stacks 011O, stacks 0AMI "recursive boundary-cycle intersection map"]
noncomputable def intersectionMap {P Q : HomologyPageTower C} (f : Hom P Q) (r : ℕ+) :
    ((P.boundary r ⊓ P.cycle r : Subobject (P.page 1)) : C) ⟶
      ((Q.boundary r ⊓ Q.cycle r : Subobject (Q.page 1)) : C) :=
  intersectionMapOf (f.app 1) (f.intersection_factors r)

/-- The explicit intersection map recovers the first-page component after the intersection
inclusions. -/
@[reassoc (attr := simp)]
theorem intersectionMapOf_arrow {P Q : HomologyPageTower C} {r : ℕ+}
    (f : P.page 1 ⟶ Q.page 1)
    (h_factors : (Q.boundary r ⊓ Q.cycle r).Factors
      ((P.boundary r ⊓ P.cycle r).arrow ≫ f)) :
    intersectionMapOf f h_factors ≫ (Q.boundary r ⊓ Q.cycle r).arrow =
      (P.boundary r ⊓ P.cycle r).arrow ≫ f := by
  exact Subobject.factorThru_arrow _ _ _

/-- The canonical intersection map recovers the first-page component after the intersection
inclusions. -/
@[reassoc (attr := simp)]
theorem intersectionMap_arrow {P Q : HomologyPageTower C} (f : Hom P Q) (r : ℕ+) :
    intersectionMap f r ≫ (Q.boundary r ⊓ Q.cycle r).arrow =
      (P.boundary r ⊓ P.cycle r).arrow ≫ f.app 1 := by
  exact intersectionMapOf_arrow _ _

/-- The explicit recursive intersection map and the restricted cycle map commute with inclusion
into the cycle stage. -/
@[reassoc]
theorem intersectionMapOf_comp_ofLE {P Q : HomologyPageTower C} (f : Hom P Q) (r : ℕ+)
    (h_factors : (Q.boundary r ⊓ Q.cycle r).Factors
      ((P.boundary r ⊓ P.cycle r).arrow ≫ f.app 1)) :
    Subobject.ofLE (P.boundary r ⊓ P.cycle r) (P.cycle r) _root_.inf_le_right ≫
        Cycle.map f r =
      intersectionMapOf (f.app 1) h_factors ≫
        Subobject.ofLE (Q.boundary r ⊓ Q.cycle r) (Q.cycle r) _root_.inf_le_right := by
  apply (cancel_mono (Q.cycle r).arrow).mp
  simp [Category.assoc]

/-- The canonical recursive intersection map and the restricted cycle map commute with inclusion
into the cycle stage. -/
@[reassoc]
theorem intersectionMap_comp_ofLE {P Q : HomologyPageTower C} (f : Hom P Q) (r : ℕ+) :
    Subobject.ofLE (P.boundary r ⊓ P.cycle r) (P.cycle r) _root_.inf_le_right ≫
        Cycle.map f r =
      intersectionMap f r ≫
        Subobject.ofLE (Q.boundary r ⊓ Q.cycle r) (Q.cycle r) _root_.inf_le_right := by
  exact f.intersection_map_comp_ofLE r

/-- The map between recursive page quotients induced by an explicit map of boundary-cycle
intersections, an explicit cycle map, and their defining square. -/
@[stacks 011O, stacks 0AMI "recursive page quotient map from an explicit square"]
noncomputable def mapOf {P Q : HomologyPageTower C} {r : ℕ+}
    (intersection :
      ((P.boundary r ⊓ P.cycle r : Subobject (P.page 1)) : C) ⟶
        ((Q.boundary r ⊓ Q.cycle r : Subobject (Q.page 1)) : C))
    (cycle : (P.cycle r : C) ⟶ (Q.cycle r : C))
    (h_comm :
      Subobject.ofLE (P.boundary r ⊓ P.cycle r) (P.cycle r) _root_.inf_le_right ≫ cycle =
        intersection ≫
          Subobject.ofLE (Q.boundary r ⊓ Q.cycle r) (Q.cycle r) _root_.inf_le_right) :
    P.pageQuotient r ⟶ Q.pageQuotient r :=
  Subobject.IntersectionQuotient.map intersection cycle h_comm

/-- The canonical map between recursive page quotients induced by a tower morphism. -/
@[stacks 011O, stacks 0AMI "recursive page quotient map"]
noncomputable def map {P Q : HomologyPageTower C} (f : Hom P Q) (r : ℕ+) :
    P.pageQuotient r ⟶ Q.pageQuotient r :=
  mapOf (intersectionMap f r) (Cycle.map f r) (f.intersection_map_comp_ofLE r)

/-- Explicit-square recursive page-quotient maps are characterized by their action on cycle
representatives. -/
@[reassoc (attr := simp)]
theorem π_naturalityOf {P Q : HomologyPageTower C} {r : ℕ+}
    (intersection :
      ((P.boundary r ⊓ P.cycle r : Subobject (P.page 1)) : C) ⟶
        ((Q.boundary r ⊓ Q.cycle r : Subobject (Q.page 1)) : C))
    (cycle : (P.cycle r : C) ⟶ (Q.cycle r : C))
    (h_comm :
      Subobject.ofLE (P.boundary r ⊓ P.cycle r) (P.cycle r) _root_.inf_le_right ≫ cycle =
        intersection ≫
          Subobject.ofLE (Q.boundary r ⊓ Q.cycle r) (Q.cycle r) _root_.inf_le_right) :
    P.pageQuotientπ r ≫ mapOf intersection cycle h_comm = cycle ≫ Q.pageQuotientπ r := by
  exact cokernel.π_desc _ _ _

/-- Recursive page-quotient maps are characterized by their action on cycle representatives. -/
@[reassoc (attr := simp)]
theorem π_naturality {P Q : HomologyPageTower C} (f : Hom P Q) (r : ℕ+) :
    P.pageQuotientπ r ≫ map f r = Cycle.map f r ≫ Q.pageQuotientπ r := by
  exact π_naturalityOf _ _ _

/-- A map of recursive page quotients is induced by a tower morphism when its composite with
the quotient projection is the corresponding map of recursive cycle representatives. -/
@[stacks 011O, stacks 0AMI "induced recursive page quotient map"]
def IsInduced {P Q : HomologyPageTower C} (f : Hom P Q) (r : ℕ+)
    (q : P.pageQuotient r ⟶ Q.pageQuotient r) : Prop :=
  P.pageQuotientπ r ≫ q = Cycle.map f r ≫ Q.pageQuotientπ r

/-- The canonical recursive page-quotient map is induced by its tower morphism. -/
@[stacks 011O, stacks 0AMI "canonical induced recursive page quotient map"]
theorem map_isInduced {P Q : HomologyPageTower C} (f : Hom P Q) (r : ℕ+) :
    IsInduced f r (map f r) := by
  exact π_naturality f r

namespace IsInduced

/-- Two recursive page-quotient maps induced by the same tower morphism are equal. -/
@[stacks 011O, stacks 0AMI "uniqueness of induced recursive page quotient maps"]
theorem unique {P Q : HomologyPageTower C} {f : Hom P Q} {r : ℕ+}
    {q q' : P.pageQuotient r ⟶ Q.pageQuotient r}
    (hq : IsInduced f r q) (hq' : IsInduced f r q') :
    q = q' := by
  apply coequalizer.hom_ext
  exact hq.trans hq'.symm

end IsInduced

/-- Recursive page-quotient maps preserve identity tower morphisms. -/
@[simp, stacks 011O, stacks 0AMI "recursive page-quotient map functoriality"]
theorem map_id (P : HomologyPageTower C) (r : ℕ+) :
    map (𝟙 P) r = 𝟙 (P.pageQuotient r) := by
  apply coequalizer.hom_ext
  change P.pageQuotientπ r ≫ map (𝟙 P) r = P.pageQuotientπ r ≫ 𝟙 _
  simp

/-- Recursive page-quotient maps preserve composition of tower morphisms. -/
@[simp, stacks 011O, stacks 0AMI "recursive page-quotient map functoriality"]
theorem map_comp {P Q R : HomologyPageTower C}
    (f : P ⟶ Q) (g : Q ⟶ R) (r : ℕ+) :
    map (f ≫ g) r = map f r ≫ map g r := by
  apply coequalizer.hom_ext
  change P.pageQuotientπ r ≫ map (f ≫ g) r = P.pageQuotientπ r ≫ (map f r ≫ map g r)
  simp [Category.assoc]

section Functor

variable (C)

/-- Taking the recursive page quotient at page `r` is functorial in homology page towers. -/
@[stacks 011O, stacks 0AMI "recursive page-quotient functor"]
noncomputable def functor (r : ℕ+) : HomologyPageTower C ⥤ C where
  obj P := P.pageQuotient r
  map f := PageQuotient.map f r
  map_id P := PageQuotient.map_id P r
  map_comp f g := PageQuotient.map_comp f g r

/-- Evaluation of the recursive page-quotient functor on an object is its page quotient. -/
@[simp]
theorem Functor.obj (r : ℕ+) (P : HomologyPageTower C) :
    (functor C r).obj P = P.pageQuotient r := by
  rfl

/-- Evaluation of the recursive page-quotient functor on a morphism is the induced quotient
map. -/
@[simp]
theorem Functor.map {P Q : HomologyPageTower C} (f : P ⟶ Q) (r : ℕ+) :
    (functor C r).map f = PageQuotient.map f r := by
  rfl

end Functor

end PageQuotient

/-! ## Infinity page -/

section Infinity

variable [LocallySmall.{v} C] [WellPowered.{v} C]
  [HasWidePullbacks.{v} C] [HasCoproducts.{v} C]
variable (P : HomologyPageTower C)

/-- The eventual cycle subobject `Z_infinity = inf_r Z_r`. -/
@[stacks 011O, stacks 0AMI "eventual cycle subobject"]
noncomputable def cycleInfinity : Subobject (P.page 1) :=
  ⨅ r : ℕ+, P.cycle r

/-- The eventual boundary subobject `B_infinity = sup_r B_r`. -/
@[stacks 011O, stacks 0AMI "eventual boundary subobject"]
noncomputable def boundaryInfinity : Subobject (P.page 1) :=
  ⨆ r : ℕ+, P.boundary r

namespace InfinityPage

/-- Eventual boundaries are contained in eventual cycles. -/
theorem boundary_le_cycle :
    P.boundaryInfinity ≤ P.cycleInfinity := by
  exact iSup_le (fun r => le_iInf (fun s => Boundary.le_cycle P r s))

end InfinityPage

/-- The infinity-page object `Z_infinity / B_infinity`. -/
@[stacks 011O, stacks 0AMI]
noncomputable def infinityPage : C :=
  Subobject.intersectionQuotient P.boundaryInfinity P.cycleInfinity

namespace InfinityPage

/-- The canonical projection from eventual cycles to the proof-free infinity-page
representative. -/
@[stacks 011O, stacks 0AMI]
noncomputable abbrev π :
    (P.cycleInfinity : C) ⟶ P.infinityPage :=
  Subobject.IntersectionQuotient.π P.boundaryInfinity P.cycleInfinity

/-- The proof-free infinity-page representative is isomorphic to the textbook quotient
`Z_infinity / B_infinity` once eventual-boundary containment is available. -/
@[stacks 011O, stacks 0AMI]
theorem isIsomorphic :
    IsIsomorphic P.infinityPage
      (cokernel
        (Subobject.ofLE P.boundaryInfinity P.cycleInfinity
          (boundary_le_cycle P))) := by
  refine ⟨cokernel.mapIso _ _
    (Subobject.isoOfEq _ _ (inf_eq_left.mpr (boundary_le_cycle P)))
    (Iso.refl _) ?_⟩
  apply (cancel_mono P.cycleInfinity.arrow).mp
  simp [Subobject.isoOfEq]

end InfinityPage

end Infinity

/-! ## Explicit limit stages -/

/-- Proof-free eventual boundary and cycle data for one homology page tower.  This data owner is
independent of the existence of arbitrary subobject suprema and infima. -/
@[stacks 011O, stacks 0AMI "explicit homology-page-tower limit-stage data"]
structure LimitStages.Data (P : HomologyPageTower C) where
  /-- The selected eventual boundary in the first page. -/
  boundary : Subobject (P.page 1)
  /-- The selected eventual cycle in the first page. -/
  cycle : Subobject (P.page 1)

/-- Explicit eventual boundary and cycle data together with their universal extremal
properties. -/
@[stacks 011O, stacks 0AMI "homology-page-tower limit stages"]
structure LimitStages (P : HomologyPageTower C) extends LimitStages.Data P where
  /-- The eventual boundary is the least upper bound of finite boundary stages. -/
  boundary_isLUB : IsLUB (Set.range P.boundary) boundary
  /-- The eventual cycle is the greatest lower bound of finite cycle stages. -/
  cycle_isGLB : IsGLB (Set.range P.cycle) cycle

namespace LimitStages.Data

variable {P : HomologyPageTower C}

/-- The proof-free infinity-page representative `Z∞ / (B∞ ⊓ Z∞)` selected by explicit data. -/
@[stacks 011O, stacks 0AMI "infinity page from explicit tower limit-stage data"]
noncomputable abbrev infinityPage (L : LimitStages.Data P) : C :=
  Subobject.intersectionQuotient L.boundary L.cycle

namespace InfinityPage

/-- The canonical projection from an explicitly selected eventual cycle to its proof-free
infinity-page representative. -/
@[stacks 011O, stacks 0AMI "explicit tower infinity-page projection"]
noncomputable abbrev π (L : LimitStages.Data P) :
    (L.cycle : C) ⟶ L.infinityPage :=
  Subobject.IntersectionQuotient.π L.boundary L.cycle

end InfinityPage

end LimitStages.Data

namespace LimitStages

variable {P : HomologyPageTower C}

/-- Every finite boundary stage is contained in the selected eventual boundary. -/
@[stacks 011O, stacks 0AMI "finite boundary stage into tower limit stage"]
theorem boundary_stage_le (L : LimitStages P) (r : ℕ+) :
    P.boundary r ≤ L.boundary := by
  exact L.boundary_isLUB.1 (Set.mem_range_self r)

/-- The selected eventual boundary is below every common upper bound of finite boundary
stages. -/
@[stacks 011O, stacks 0AMI "least tower boundary limit stage"]
theorem boundary_least (L : LimitStages P) (B : Subobject (P.page 1))
    (hB : ∀ r : ℕ+, P.boundary r ≤ B) :
    L.boundary ≤ B := by
  apply L.boundary_isLUB.2
  rintro _ ⟨r, rfl⟩
  exact hB r

/-- The selected eventual cycle is contained in every finite cycle stage. -/
@[stacks 011O, stacks 0AMI "tower limit cycle stage into a finite cycle stage"]
theorem cycle_le_stage (L : LimitStages P) (r : ℕ+) :
    L.cycle ≤ P.cycle r := by
  exact L.cycle_isGLB.1 (Set.mem_range_self r)

/-- Every common lower bound of finite cycle stages is below the selected eventual cycle. -/
@[stacks 011O, stacks 0AMI "greatest tower cycle limit stage"]
theorem cycle_greatest (L : LimitStages P) (Z : Subobject (P.page 1))
    (hZ : ∀ r : ℕ+, Z ≤ P.cycle r) :
    Z ≤ L.cycle := by
  apply L.cycle_isGLB.2
  rintro _ ⟨r, rfl⟩
  exact hZ r

/-- The selected eventual boundary is contained in the selected eventual cycle.  This is
derived from the extremal properties and the finite-stage boundary-to-cycle comparison. -/
@[stacks 011O, stacks 0AMI "tower limit boundary contained in cycle"]
theorem boundary_le_cycle (L : LimitStages P) : L.boundary ≤ L.cycle := by
  apply L.boundary_least
  intro r
  exact L.cycle_greatest _ (fun s => Boundary.le_cycle P r s)

/-- Eventual boundaries are independent of the selected complete limit-stage package. -/
@[stacks 011O, stacks 0AMI "uniqueness of tower eventual boundaries"]
theorem boundary_eq (L L' : LimitStages P) : L.boundary = L'.boundary := by
  exact L.boundary_isLUB.unique L'.boundary_isLUB

/-- Eventual cycles are independent of the selected complete limit-stage package. -/
@[stacks 011O, stacks 0AMI "uniqueness of tower eventual cycles"]
theorem cycle_eq (L L' : LimitStages P) : L.cycle = L'.cycle := by
  exact L.cycle_isGLB.unique L'.cycle_isGLB

/-- Complete limit-stage packages are unique; only proof-free data can carry a genuine choice. -/
@[stacks 011O, stacks 0AMI "uniqueness of tower limit stages"]
theorem eq (L L' : LimitStages P) : L = L' := by
  have hB := boundary_eq L L'
  have hZ := cycle_eq L L'
  rcases L with ⟨⟨B, Z⟩, hB₁, hZ₁⟩
  rcases L' with ⟨⟨B', Z'⟩, hB₂, hZ₂⟩
  change B = B' at hB
  change Z = Z' at hZ
  cases hB
  cases hZ
  rfl

/-- The proof-free infinity-page representative selected by complete tower limit stages. -/
@[stacks 011O, stacks 0AMI "infinity page from complete tower limit stages"]
noncomputable abbrev infinityPage (L : LimitStages P) : C :=
  L.toData.infinityPage

namespace InfinityPage

/-- The canonical projection from a complete tower limit stage to its infinity-page
representative. -/
@[stacks 011O, stacks 0AMI "tower limit-stage infinity-page projection"]
noncomputable abbrev π (L : LimitStages P) :
    (L.cycle : C) ⟶ L.infinityPage :=
  LimitStages.Data.InfinityPage.π L.toData

end InfinityPage

/-- The proof-free infinity-page representative is isomorphic to the textbook quotient
`Z∞ / B∞` once the derived boundary containment is used. -/
@[stacks 011O, stacks 0AMI "tower infinity-page quotient comparison"]
theorem infinityPage_isIsomorphic (L : LimitStages P) :
    IsIsomorphic L.infinityPage
      (cokernel (Subobject.ofLE L.boundary L.cycle L.boundary_le_cycle)) := by
  refine ⟨cokernel.mapIso _ _
    (Subobject.isoOfEq _ _ (inf_eq_left.mpr L.boundary_le_cycle))
    (Iso.refl _) ?_⟩
  apply (cancel_mono L.cycle.arrow).mp
  simp [Subobject.isoOfEq]

section Canonical

variable [LocallySmall.{v} C] [WellPowered.{v} C]
  [HasWidePullbacks.{v} C] [HasCoproducts.{v} C]

/-- The canonical eventual boundary is the least upper bound of finite boundary stages. -/
@[stacks 011O, stacks 0AMI "canonical tower boundary least upper bound"]
theorem boundaryInfinity_isLUB (P : HomologyPageTower C) :
    IsLUB (Set.range P.boundary) P.boundaryInfinity := by
  exact isLUB_iSup

/-- The canonical eventual cycle is the greatest lower bound of finite cycle stages. -/
@[stacks 011O, stacks 0AMI "canonical tower cycle greatest lower bound"]
theorem cycleInfinity_isGLB (P : HomologyPageTower C) :
    IsGLB (Set.range P.cycle) P.cycleInfinity := by
  exact isGLB_iInf

/-- The canonical complete subobject lattice provides the tower limit stages. -/
@[stacks 011O, stacks 0AMI "canonical homology-page-tower limit stages"]
noncomputable def canonical (P : HomologyPageTower C) : LimitStages P where
  toData :=
    { boundary := P.boundaryInfinity
      cycle := P.cycleInfinity }
  boundary_isLUB := boundaryInfinity_isLUB P
  cycle_isGLB := cycleInfinity_isGLB P

/-- The boundary component of canonical tower limit stages is the existing supremum-defined
eventual boundary. -/
@[simp, stacks 011O, stacks 0AMI "canonical tower limit boundary"]
theorem canonical_boundary (P : HomologyPageTower C) :
    (canonical P).boundary = P.boundaryInfinity := by
  rfl

/-- The cycle component of canonical tower limit stages is the existing infimum-defined
eventual cycle. -/
@[simp, stacks 011O, stacks 0AMI "canonical tower limit cycle"]
theorem canonical_cycle (P : HomologyPageTower C) :
    (canonical P).cycle = P.cycleInfinity := by
  rfl

end Canonical

end LimitStages

end HomologyPageTower

end CategoryTheory
