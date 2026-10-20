module

public import ReasLib.Topology.Stratification.Indexed
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Reduced.Structure
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FiniteLocallyFree
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.LocallyQuasiFinite
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocallyOfFinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiberDegree

/-!
# Fibre-degree stratifications of morphisms from schemes to algebraic spaces

This file defines finite closed filtrations of `|X|` whose strata universally classify the
ranks of finite locally free base changes of a morphism `ofOver W ⟶ X`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X : AlgebraicSpace S} {W : Over S}

/-- A rank-indexed finite closed filtration of `|X|` whose strata universally classify the
rank of every base change of `f : ofOver W ⟶ X`. -/
structure DegreeStratification (f : ofOver W ⟶ X) where
  /-- An upper bound for the ranks occurring in the stratification. -/
  bound : ℕ
  /-- The closed stages, with index zero representing `Z₋₁`. -/
  closedStage : Fin (bound + 2) → Set (Points X)
  /-- Every stage of the filtration is closed. -/
  isClosed_closedStage : ∀ i, IsClosed (closedStage i)
  /-- The closed stages form an increasing family. -/
  monotone_closedStage : Monotone closedStage
  /-- The initial stage `Z₋₁` is empty. -/
  closedStage_zero : closedStage 0 = ∅
  /-- The final stage is the whole space of points of `X`. -/
  closedStage_last : closedStage (Fin.last (bound + 1)) = Set.univ
  /-- A base change has rank `r` exactly when its set-theoretic image lies in the
  difference `Zᵣ \ Zᵣ₋₁`. -/
  pullbackRank_iff_range_subset :
    ∀ {T : AlgebraicSpace S} (r : Fin (bound + 1)) (g : T ⟶ X),
      FiniteLocallyFreeOfRank (pullback.snd f g) (r : ℕ) ↔
        Set.range (Points.map g) ⊆ closedStage r.succ \ closedStage r.castSucc

namespace DegreeStratification

/-- Construct a degree stratification from explicit closed stages and their defining laws. -/
def ofStages (f : ofOver W ⟶ X) (bound : ℕ)
    (closedStage : Fin (bound + 2) → Set (Points X))
    (isClosed : ∀ i, IsClosed (closedStage i)) (monotone : Monotone closedStage)
    (zero : closedStage 0 = ∅)
    (last : closedStage (Fin.last (bound + 1)) = Set.univ)
    (rank : ∀ {T : AlgebraicSpace S} (r : Fin (bound + 1)) (g : T ⟶ X),
      FiniteLocallyFreeOfRank (pullback.snd f g) (r : ℕ) ↔
        Set.range (Points.map g) ⊆ closedStage r.succ \ closedStage r.castSucc) :
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
theorem ofStages_closedStage (f : ofOver W ⟶ X) (bound : ℕ)
    (closedStage : Fin (bound + 2) → Set (Points X))
    (isClosed : ∀ i, IsClosed (closedStage i)) (monotone : Monotone closedStage)
    (zero : closedStage 0 = ∅)
    (last : closedStage (Fin.last (bound + 1)) = Set.univ)
    (rank : ∀ {T : AlgebraicSpace S} (r : Fin (bound + 1)) (g : T ⟶ X),
      FiniteLocallyFreeOfRank (pullback.snd f g) (r : ℕ) ↔
        Set.range (Points.map g) ⊆ closedStage r.succ \ closedStage r.castSucc) :
    (ofStages f bound closedStage isClosed monotone zero last rank).closedStage =
      closedStage := sorry

/-- The rank-`r` stratum `Zᵣ \ Zᵣ₋₁` of a degree stratification. -/
def stratum {f : ofOver W ⟶ X} (D : DegreeStratification f) (r : Fin (D.bound + 1)) :
    Set (Points X) :=
  D.closedStage r.succ \ D.closedStage r.castSucc

/-- The rank stratum is the difference of its consecutive closed stages. -/
theorem stratum_def {f : ofOver W ⟶ X} (D : DegreeStratification f)
    (r : Fin (D.bound + 1)) :
    D.stratum r = D.closedStage r.succ \ D.closedStage r.castSucc := sorry

/-- The reduced induced closed subspace on the `i`-th closed stage. -/
def closedSubspace {f : ofOver W ⟶ X} (D : DegreeStratification f)
    (i : Fin (D.bound + 2)) : ClosedSubspace X :=
  (ClosedSubspaceStructure.reduced ⟨D.closedStage i, D.isClosed_closedStage i⟩).subspace

/-- The underlying point-set of the reduced closed subspace on stage `i` is that stage. -/
theorem closedSubspace_pointsSet {f : ofOver W ⟶ X} (D : DegreeStratification f)
    (i : Fin (D.bound + 2)) :
    (D.closedSubspace i).pointsSet = D.closedStage i := sorry

/-- The closed subspace on stage `i` is reduced in the étale-local sense. -/
theorem closedSubspace_isReduced {f : ofOver W ⟶ X} (D : DegreeStratification f)
    (i : Fin (D.bound + 2)) :
    hasEtaleLocal (AlgebraicGeometry.IsReduced : ObjectProperty Scheme.{u})
      (D.closedSubspace i).X := sorry

/-- The rank strata form an indexed locally closed stratification of `|X|`. -/
theorem isStratification {f : ofOver W ⟶ X} (D : DegreeStratification f) :
    IsStratification D.stratum := sorry

/-- A base change has rank `r` exactly when its image lies in the rank-`r` stratum. -/
theorem pullbackRank_iff {f : ofOver W ⟶ X} (D : DegreeStratification f)
    (r : Fin (D.bound + 1)) {T : AlgebraicSpace S} (g : T ⟶ X) :
    FiniteLocallyFreeOfRank (pullback.snd f g) (r : ℕ) ↔
      Set.range (Points.map g) ⊆ D.stratum r := sorry

/-- The closedness, order, endpoint, and universal rank conditions of a degree
stratification. -/
theorem spec {f : ofOver W ⟶ X} (D : DegreeStratification f) :
    (∀ i, IsClosed (D.closedStage i)) ∧
      Monotone D.closedStage ∧
      D.closedStage 0 = ∅ ∧
      D.closedStage (Fin.last (D.bound + 1)) = Set.univ ∧
      ∀ {T : AlgebraicSpace S} (r : Fin (D.bound + 1)) (g : T ⟶ X),
        FiniteLocallyFreeOfRank (pullback.snd f g) (r : ℕ) ↔
          Set.range (Points.map g) ⊆ D.stratum r := sorry

/-- Rank strata of equal rank in two degree stratifications of `f` coincide. -/
theorem unique_stratum {f : ofOver W ⟶ X} (D D' : DegreeStratification f)
    {r : ℕ} (hr : r < D.bound + 1) (hr' : r < D'.bound + 1) :
    D.stratum ⟨r, hr⟩ = D'.stratum ⟨r, hr'⟩ := sorry

end DegreeStratification

/-- Every flat, locally finitely presented, separated, locally quasi-finite morphism from a
scheme to an algebraic space with universally bounded fibres admits a finite closed degree
stratification whose rank strata universally classify finite locally free base changes. -/
theorem exists_degreeStratification (f : ofOver W ⟶ X) [Flat f]
    [LocallyOfFinitePresentation f] [Separated f] [LocallyQuasiFinite f]
    (hbounded : universallyBoundedFibres f) :
    Nonempty (DegreeStratification f) := sorry

end AlgebraicGeometry.AlgebraicSpace

