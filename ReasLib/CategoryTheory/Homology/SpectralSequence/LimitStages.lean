/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Homology.SpectralSequence.PageFiltration
public import ReasLib.CategoryTheory.Subobject.Quotient.Intersection

/-!
# Limit Stages of a Spectral Sequence

@stack 012Q

Ordinary spectral-sequence limit stages are the coordinatewise specialization of the neutral
`HomologyPageTower.LimitStages` API.  This file keeps the `pq`-indexed surface convenient for
spectral-sequence consumers without duplicating the universal-property machinery.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe v u

namespace CategoryTheory
namespace SpectralSequence

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {κ : Type*} {c : ℤ → ComplexShape κ}

/-- Proof-free eventual boundary and cycle data for every graded entry of a spectral sequence.
The one-entry owner is `HomologyPageTower.LimitStages.Data`. -/
@[stacks 012Q "eventual boundary and cycle data"]
abbrev LimitStages.Data (E : SpectralSequence C c 1) :=
  ∀ pq : κ, HomologyPageTower.LimitStages.Data (E.homologyPageTower pq)

/-- Complete eventual boundary and cycle data for every graded entry of a spectral sequence.
The one-entry owner is `HomologyPageTower.LimitStages`. -/
@[stacks 012Q "eventual boundary and cycle limit stages"]
abbrev LimitStages (E : SpectralSequence C c 1) :=
  ∀ pq : κ, HomologyPageTower.LimitStages (E.homologyPageTower pq)

namespace LimitStages.Data

variable {E : SpectralSequence C c 1}

/-- The eventual boundary at one grading. -/
@[stacks 012Q "eventual boundary at a spectral-sequence grading"]
abbrev boundary (L : LimitStages.Data E) (pq : κ) : Subobject (E.pageObject pq 1) :=
  (L pq).boundary

/-- The eventual cycle at one grading. -/
@[stacks 012Q "eventual cycle at a spectral-sequence grading"]
abbrev cycle (L : LimitStages.Data E) (pq : κ) : Subobject (E.pageObject pq 1) :=
  (L pq).cycle

/-- The proof-free infinity-page representative selected by data at one grading. -/
@[stacks 012Q "infinity page from explicit limit-stage data"]
noncomputable abbrev infinityPage (L : LimitStages.Data E) (pq : κ) : C :=
  (L pq).infinityPage

namespace InfinityPage

/-- The canonical projection from the selected eventual cycle to the proof-free infinity-page
representative at one grading. -/
@[stacks 012Q "explicit limit-stage infinity-page projection"]
noncomputable abbrev π (L : LimitStages.Data E) (pq : κ) :
    (L.cycle pq : C) ⟶ L.infinityPage pq :=
  HomologyPageTower.LimitStages.Data.InfinityPage.π (L pq)

end InfinityPage

/-- The bigraded infinity-page object selected by explicit limit-stage data. -/
@[stacks 012Q "infinity page from explicit limit stages"]
noncomputable abbrev infinityPageObject (L : LimitStages.Data E) : GradedObject κ C :=
  fun pq ↦ L.infinityPage pq

end LimitStages.Data

namespace LimitStages

variable {E : SpectralSequence C c 1}

/-- Forget the universal-property proofs from complete spectral-sequence limit stages. -/
@[stacks 012Q "proof-free spectral-sequence limit-stage data"]
abbrev toData (L : LimitStages E) : LimitStages.Data E :=
  fun pq ↦ (L pq).toData

/-- The selected eventual boundary at one grading. -/
@[stacks 012Q "spectral-sequence limit boundary"]
abbrev boundary (L : LimitStages E) (pq : κ) : Subobject (E.pageObject pq 1) :=
  (L pq).boundary

/-- The selected eventual cycle at one grading. -/
@[stacks 012Q "spectral-sequence limit cycle"]
abbrev cycle (L : LimitStages E) (pq : κ) : Subobject (E.pageObject pq 1) :=
  (L pq).cycle

/-- Every finite boundary stage is contained in the selected eventual boundary. -/
@[stacks 012Q "finite boundary stage into spectral-sequence limit stage"]
theorem boundary_stage_le (L : LimitStages E) (pq : κ) (r : ℕ+) :
    E.boundary pq r ≤ L.boundary pq := sorry

/-- The selected eventual boundary is below every common upper bound of finite boundary stages. -/
@[stacks 012Q "least spectral-sequence boundary limit stage"]
theorem boundary_least (L : LimitStages E) (pq : κ) (B : Subobject (E.pageObject pq 1))
    (hB : ∀ r : ℕ+, E.boundary pq r ≤ B) :
    L.boundary pq ≤ B := sorry

/-- The selected eventual cycle is contained in every finite cycle stage. -/
@[stacks 012Q "spectral-sequence limit cycle into a finite cycle stage"]
theorem cycle_le_stage (L : LimitStages E) (pq : κ) (r : ℕ+) :
    L.cycle pq ≤ E.cycle pq r := sorry

/-- Every common lower bound of finite cycle stages is below the selected eventual cycle. -/
@[stacks 012Q "greatest spectral-sequence cycle limit stage"]
theorem cycle_greatest (L : LimitStages E) (pq : κ) (Z : Subobject (E.pageObject pq 1))
    (hZ : ∀ r : ℕ+, Z ≤ E.cycle pq r) :
    Z ≤ L.cycle pq := sorry

/-- The selected eventual boundary is contained in the selected eventual cycle. -/
@[stacks 012Q "spectral-sequence limit boundary contained in cycle"]
theorem boundary_le_cycle (L : LimitStages E) (pq : κ) :
    L.boundary pq ≤ L.cycle pq := sorry

/-- Eventual boundaries are independent of the complete limit-stage package. -/
@[stacks 012Q "uniqueness of eventual boundaries"]
theorem boundary_eq (L L' : LimitStages E) (pq : κ) :
    L.boundary pq = L'.boundary pq := sorry

/-- Eventual cycles are independent of the complete limit-stage package. -/
@[stacks 012Q "uniqueness of eventual cycles"]
theorem cycle_eq (L L' : LimitStages E) (pq : κ) :
    L.cycle pq = L'.cycle pq := sorry

/-- Complete spectral-sequence limit-stage packages are unique. -/
@[stacks 012Q "uniqueness of complete limit stages"]
theorem eq (L L' : LimitStages E) : L = L' := sorry

/-- The proof-free infinity-page representative selected by complete limit-stage data. -/
@[stacks 012Q "infinity page from complete limit stages"]
noncomputable abbrev infinityPage (L : LimitStages E) (pq : κ) : C :=
  L.toData.infinityPage pq

/-- The bigraded proof-free infinity page selected by complete limit-stage data. -/
@[stacks 012Q "bigraded infinity page from complete limit stages"]
noncomputable abbrev infinityPageObject (L : LimitStages E) : GradedObject κ C :=
  L.toData.infinityPageObject

namespace InfinityPage

/-- The canonical projection from a complete limit stage to its infinity-page representative. -/
@[stacks 012Q "limit-stage infinity-page projection"]
noncomputable abbrev π (L : LimitStages E) (pq : κ) :
    (L.cycle pq : C) ⟶ L.infinityPage pq :=
  LimitStages.Data.InfinityPage.π L.toData pq

end InfinityPage

/-- The proof-free infinity-page representative is isomorphic to the textbook quotient
`Z∞ / B∞` once the derived boundary containment is used. -/
@[stacks 012Q "infinity-page quotient comparison"]
theorem infinityPage_isIsomorphic (L : LimitStages E) (pq : κ) :
    IsIsomorphic (L.infinityPage pq)
      (cokernel (Subobject.ofLE (L.boundary pq) (L.cycle pq) (L.boundary_le_cycle pq))) := sorry

end LimitStages

section Canonical

variable [LocallySmall.{v} C] [WellPowered.{v} C]
  [HasWidePullbacks.{v} C] [HasCoproducts.{v} C]

/-- The canonical complete subobject lattice gives coordinatewise spectral-sequence limit stages. -/
@[stacks 012Q "canonical limit stages"]
noncomputable def canonicalLimitStages (E : SpectralSequence C c 1) : LimitStages E :=
  fun pq ↦ HomologyPageTower.LimitStages.canonical (E.homologyPageTower pq)

/-- The boundary component of canonical spectral-sequence limit stages is the existing
supremum-defined eventual boundary. -/
@[simp, stacks 012Q "canonical spectral-sequence limit boundary"]
theorem canonicalLimitStages_boundary (E : SpectralSequence C c 1) (pq : κ) :
    (canonicalLimitStages E).boundary pq = E.boundaryInfinity pq := sorry

/-- The cycle component of canonical spectral-sequence limit stages is the existing
infimum-defined eventual cycle. -/
@[simp, stacks 012Q "canonical spectral-sequence limit cycle"]
theorem canonicalLimitStages_cycle (E : SpectralSequence C c 1) (pq : κ) :
    (canonicalLimitStages E).cycle pq = E.cycleInfinity pq := sorry

/-- The infinity-page entry from canonical spectral-sequence limit stages is the existing
canonical infinity-page entry. -/
@[simp, stacks 012Q "canonical spectral-sequence infinity page"]
theorem canonicalLimitStages_infinityPage (E : SpectralSequence C c 1) (pq : κ) :
    (canonicalLimitStages E).infinityPage pq = E.infinityPage pq := sorry

end Canonical

end SpectralSequence
end CategoryTheory
