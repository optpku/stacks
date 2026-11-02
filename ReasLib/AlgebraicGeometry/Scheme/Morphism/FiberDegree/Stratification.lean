/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberDegree
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteLocallyFree.Basic
public import ReasLib.Topology.Stratification.Indexed

/-!
# Fibre-degree stratifications of scheme morphisms

This file defines finite closed filtrations whose strata universally classify the ranks of
finite locally free base changes of a scheme morphism.
-/

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry
namespace Scheme.Hom

variable {X S : Scheme.{u}}

/-- A rank-indexed finite closed filtration of the target of `f` whose strata universally
classify the rank of every base change of `f`. -/
structure DegreeStratification (f : X ⟶ S) where
  /-- An upper bound for the ranks occurring in the stratification. -/
  bound : ℕ
  /-- The closed stages, with index zero representing `Z₋₁`. -/
  closedStage : Fin (bound + 2) → Set S
  /-- Every stage of the filtration is closed. -/
  isClosed_closedStage : ∀ i, IsClosed (closedStage i)
  /-- The closed stages form an increasing family. -/
  monotone_closedStage : Monotone closedStage
  /-- The initial stage `Z₋₁` is empty. -/
  closedStage_zero : closedStage 0 = ∅
  /-- The final stage is the whole target. -/
  closedStage_last : closedStage (Fin.last (bound + 1)) = Set.univ
  /-- A base change has rank `r` exactly when its set-theoretic image lies in the
  difference `Zᵣ \ Zᵣ₋₁`. -/
  pullbackRank_iff_range_subset :
    ∀ {T : Scheme.{u}} (r : Fin (bound + 1)) (g : T ⟶ S),
      IsFiniteLocallyFreeOfRank (pullback.snd f g) (r : ℕ) ↔
        Set.range g.base ⊆ closedStage r.succ \ closedStage r.castSucc

namespace DegreeStratification

/-- Construct a degree stratification from explicit closed stages and their defining laws. -/
def ofStages (f : X ⟶ S) (bound : ℕ) (closedStage : Fin (bound + 2) → Set S)
    (isClosed : ∀ i, IsClosed (closedStage i)) (monotone : Monotone closedStage)
    (zero : closedStage 0 = ∅)
    (last : closedStage (Fin.last (bound + 1)) = Set.univ)
    (rank : ∀ {T : Scheme.{u}} (r : Fin (bound + 1)) (g : T ⟶ S),
      IsFiniteLocallyFreeOfRank (pullback.snd f g) (r : ℕ) ↔
        Set.range g.base ⊆ closedStage r.succ \ closedStage r.castSucc) :
    DegreeStratification f where
  bound := bound
  closedStage := closedStage
  isClosed_closedStage := isClosed
  monotone_closedStage := monotone
  closedStage_zero := zero
  closedStage_last := last
  pullbackRank_iff_range_subset := rank

/-- The closed stages of a degree stratification built by `ofStages` are the supplied stages. -/
@[simp]
theorem ofStages_closedStage (f : X ⟶ S) (bound : ℕ)
    (closedStage : Fin (bound + 2) → Set S)
    (isClosed : ∀ i, IsClosed (closedStage i)) (monotone : Monotone closedStage)
    (zero : closedStage 0 = ∅)
    (last : closedStage (Fin.last (bound + 1)) = Set.univ)
    (rank : ∀ {T : Scheme.{u}} (r : Fin (bound + 1)) (g : T ⟶ S),
      IsFiniteLocallyFreeOfRank (pullback.snd f g) (r : ℕ) ↔
        Set.range g.base ⊆ closedStage r.succ \ closedStage r.castSucc) :
    (ofStages f bound closedStage isClosed monotone zero last rank).closedStage = closedStage := rfl

/-- The rank-`r` stratum `Zᵣ \ Zᵣ₋₁` of a degree stratification. -/
def stratum {f : X ⟶ S} (D : DegreeStratification f) (r : Fin (D.bound + 1)) : Set S :=
  D.closedStage r.succ \ D.closedStage r.castSucc

/-- The rank stratum is the difference of its consecutive closed stages. -/
theorem stratum_def {f : X ⟶ S} (D : DegreeStratification f)
    (r : Fin (D.bound + 1)) :
    D.stratum r = D.closedStage r.succ \ D.closedStage r.castSucc := rfl

/-- The rank strata form an indexed locally closed stratification of the target. -/
theorem isStratification {f : X ⟶ S} (D : DegreeStratification f) :
    IsStratification D.stratum := by
  classical
  have mem_stage : ∀ (i : Fin (D.bound + 2)) {x : S}, x ∈ D.closedStage i →
      ∃ r : Fin (D.bound + 1), r.succ ≤ i ∧ x ∈ D.stratum r := by
    intro i
    induction i using Fin.induction with
    | zero =>
        intro x hx
        rw [D.closedStage_zero] at hx
        exact hx.elim
    | succ i ih =>
        intro x hx
        by_cases hx' : x ∈ D.closedStage i.castSucc
        · obtain ⟨r, hr, hxr⟩ := ih hx'
          exact ⟨r, hr.trans (le_of_lt i.castSucc_lt_succ), hxr⟩
        · exact ⟨i, le_rfl, hx, hx'⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j hij
    rw [Set.disjoint_left]
    intro x hxi hxj
    rcases lt_or_gt_of_ne hij with h | h
    · exact hxj.2 (D.monotone_closedStage (Nat.succ_le_of_lt h) hxi.1)
    · exact hxi.2 (D.monotone_closedStage (Nat.succ_le_of_lt h) hxj.1)
  · apply Set.eq_univ_of_forall
    intro x
    have hx : x ∈ D.closedStage (Fin.last (D.bound + 1)) := by
      rw [D.closedStage_last]
      trivial
    obtain ⟨r, _, hxr⟩ := mem_stage _ hx
    exact Set.mem_iUnion.mpr ⟨r, hxr⟩
  · intro r
    refine ⟨(D.closedStage r.castSucc)ᶜ, D.closedStage r.succ,
      (D.isClosed_closedStage _).isOpen_compl, D.isClosed_closedStage _, ?_⟩
    ext x
    exact and_comm
  · intro j x hx
    have hxj : x ∈ D.closedStage j.succ :=
      closure_minimal (fun _ h ↦ h.1) (D.isClosed_closedStage _) hx
    obtain ⟨i, hij, hxi⟩ := mem_stage _ hxj
    refine Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨?_, hxi⟩⟩
    exact Nat.le_of_succ_le_succ hij

/-- The finite indexed stratification underlying a degree stratification. -/
def toFiniteStratification {f : X ⟶ S} (D : DegreeStratification f) :
    FiniteStratification S :=
  FiniteStratification.ofStrata D.stratum D.isStratification

/-- The strata of the underlying finite stratification are the rank strata. -/
theorem toFiniteStratification_strata {f : X ⟶ S} (D : DegreeStratification f)
    (r : Fin (D.bound + 1)) :
    D.toFiniteStratification.strata r = D.stratum r := rfl

/-- A base change has rank `r` exactly when its image lies in the rank-`r` stratum. -/
theorem pullbackRank_iff {f : X ⟶ S} (D : DegreeStratification f)
    (r : Fin (D.bound + 1)) {T : Scheme.{u}} (g : T ⟶ S) :
    IsFiniteLocallyFreeOfRank (pullback.snd f g) (r : ℕ) ↔
      Set.range g.base ⊆ D.stratum r :=
  D.pullbackRank_iff_range_subset r g

/-- The closedness, order, endpoint, and universal rank conditions of a degree stratification. -/
theorem spec {f : X ⟶ S} (D : DegreeStratification f) :
    (∀ i, IsClosed (D.closedStage i)) ∧
      Monotone D.closedStage ∧
      D.closedStage 0 = ∅ ∧
      D.closedStage (Fin.last (D.bound + 1)) = Set.univ ∧
      ∀ {T : Scheme.{u}} (r : Fin (D.bound + 1)) (g : T ⟶ S),
        IsFiniteLocallyFreeOfRank (pullback.snd f g) (r : ℕ) ↔
          Set.range g.base ⊆ D.stratum r :=
  ⟨D.isClosed_closedStage, D.monotone_closedStage, D.closedStage_zero,
    D.closedStage_last, fun r g ↦ D.pullbackRank_iff r g⟩

end DegreeStratification

/-- Every flat, locally finitely presented, separated, locally quasi-finite scheme morphism
with universally bounded fibres admits a finite closed degree stratification whose rank strata
universally classify finite locally free base changes. -/
theorem exists_degreeStratification (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f]
    [IsSeparated f] [LocallyQuasiFinite f] (hbounded : universallyBoundedFibres f) :
    Nonempty (DegreeStratification f) := sorry

end Scheme.Hom
end AlgebraicGeometry
