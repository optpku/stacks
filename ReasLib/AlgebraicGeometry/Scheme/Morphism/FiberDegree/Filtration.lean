/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Limit.FiniteLocallyFree
public import ReasLib.AlgebraicGeometry.Scheme.LocallyClosedReduction
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberDegree.LocallyQuasiFinite
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberDegree.Stratification
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite

/-!
# Fibre-degree filtrations of quasi-finite scheme morphisms

This file defines exhaustive closed filtrations whose strata universally classify the ranks of
finite locally free base changes and records their existence for quasi-finite morphisms.
-/

@[expose] public section

open CategoryTheory Limits TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry
namespace Scheme.Hom

variable {X S : Scheme.{u}}

/-- The rank-`r` stratum determined by closed stages indexed so that stage zero is `Z₋₁`. -/
def rankStratum (closedStage : ℕ → Set S) (r : ℕ) : Set S :=
  closedStage (r + 1) \ closedStage r

/-- The rank stratum is the difference of the two consecutive closed stages. -/
theorem rankStratum_def (closedStage : ℕ → Set S) (r : ℕ) :
    rankStratum closedStage r = closedStage (r + 1) \ closedStage r := sorry

/-- Successive differences in a closed filtration are locally closed. -/
theorem rankStratum_isLocallyClosed (closedStage : ℕ → Set S)
    (isClosed : ∀ n, IsClosed (closedStage n)) (r : ℕ) :
    IsLocallyClosed (rankStratum closedStage r) := sorry

/-- An increasing exhaustive closed filtration whose strata universally classify the ranks of
all base changes of a scheme morphism. Stage zero represents `Z₋₁`, so the rank-`r` stratum is
the difference of stages `r + 1` and `r`. -/
structure DegreeFiltration (f : X ⟶ S) where
  /-- The closed stages, with index zero representing `Z₋₁`. -/
  closedStage : ℕ → Set S
  /-- Every stage of the filtration is closed. -/
  isClosed_closedStage : ∀ n, IsClosed (closedStage n)
  /-- The closed stages form an increasing family. -/
  monotone_closedStage : Monotone closedStage
  /-- The initial stage `Z₋₁` is empty. -/
  closedStage_zero : closedStage 0 = ∅
  /-- The closed stages exhaust the target. -/
  iUnion_closedStage : (⋃ n, closedStage n) = Set.univ
  /-- Every base change has rank `r` exactly when its image lies in the rank-`r` stratum. -/
  pullbackRank_iff_range_subset :
    ∀ {T : Scheme.{u}} (r : ℕ) (g : T ⟶ S),
      IsFiniteLocallyFreeOfRank (pullback.snd f g) r ↔
        Set.range g.base ⊆ rankStratum closedStage r
  /-- The canonical inclusion of every reduced rank stratum is quasi-compact. -/
  quasiCompact_stratumι :
    ∀ r, QuasiCompact (LocallyClosedReduction.ι
      ⟨rankStratum closedStage r,
        rankStratum_isLocallyClosed closedStage isClosed_closedStage r⟩)

namespace DegreeFiltration

/-- Construct a degree filtration from explicit closed stages and proofs of its defining laws. -/
def ofStages (f : X ⟶ S) (closedStage : ℕ → Set S)
    (isClosed : ∀ n, IsClosed (closedStage n)) (monotone : Monotone closedStage)
    (zero : closedStage 0 = ∅) (exhaustive : (⋃ n, closedStage n) = Set.univ)
    (rank : ∀ {T : Scheme.{u}} (r : ℕ) (g : T ⟶ S),
      IsFiniteLocallyFreeOfRank (pullback.snd f g) r ↔
        Set.range g.base ⊆ rankStratum closedStage r)
    (quasiCompact : ∀ r, QuasiCompact (LocallyClosedReduction.ι
      ⟨rankStratum closedStage r, rankStratum_isLocallyClosed closedStage isClosed r⟩)) :
    DegreeFiltration f where
  closedStage := closedStage
  isClosed_closedStage := isClosed
  monotone_closedStage := monotone
  closedStage_zero := zero
  iUnion_closedStage := exhaustive
  pullbackRank_iff_range_subset := rank
  quasiCompact_stratumι := quasiCompact

/-- The rank-`r` stratum of a degree filtration. -/
def stratum {f : X ⟶ S} (D : DegreeFiltration f) (r : ℕ) : Set S :=
  rankStratum D.closedStage r

/-- Every rank stratum of a degree filtration is locally closed. -/
theorem stratum_isLocallyClosed {f : X ⟶ S} (D : DegreeFiltration f) (r : ℕ) :
    IsLocallyClosed (D.stratum r) := sorry

/-- The rank stratum bundled as a locally closed subset of the target. -/
def stratumLocallyClosed {f : X ⟶ S} (D : DegreeFiltration f) (r : ℕ) :
    LocallyCloseds S :=
  ⟨D.stratum r, D.stratum_isLocallyClosed r⟩

/-- The reduced induced scheme carried by a rank stratum. -/
abbrev stratumScheme {f : X ⟶ S} (D : DegreeFiltration f) (r : ℕ) : Scheme.{u} :=
  LocallyClosedReduction.scheme (D.stratumLocallyClosed r)

/-- The canonical immersion of a reduced rank stratum into the target scheme. -/
abbrev stratumι {f : X ⟶ S} (D : DegreeFiltration f) (r : ℕ) :
    D.stratumScheme r ⟶ S :=
  LocallyClosedReduction.ι (D.stratumLocallyClosed r)

/-- The defining closure, order, exhaustion, universal rank, and quasi-compactness conditions of a
degree filtration. -/
theorem spec {f : X ⟶ S} (D : DegreeFiltration f) :
    (∀ n, IsClosed (D.closedStage n)) ∧
      Monotone D.closedStage ∧
      D.closedStage 0 = ∅ ∧
      (⋃ n, D.closedStage n) = Set.univ ∧
      (∀ {T : Scheme.{u}} (r : ℕ) (g : T ⟶ S),
        IsFiniteLocallyFreeOfRank (pullback.snd f g) r ↔
          Set.range g.base ⊆ D.stratum r) ∧
      ∀ r, QuasiCompact (D.stratumι r) := sorry

/-- The rank strata form an indexed locally closed stratification of the target. -/
theorem isStratification {f : X ⟶ S} (D : DegreeFiltration f) :
    IsStratification D.stratum := sorry

/-- A base change has rank `r` exactly when its image lies in the rank-`r` stratum. -/
theorem pullbackRank_iff {f : X ⟶ S} (D : DegreeFiltration f) (r : ℕ)
    {T : Scheme.{u}} (g : T ⟶ S) :
    IsFiniteLocallyFreeOfRank (pullback.snd f g) r ↔
      Set.range g.base ⊆ D.stratum r := sorry

/-- The canonical inclusion of every reduced rank stratum is quasi-compact. -/
theorem stratumι_quasiCompact {f : X ⟶ S} (D : DegreeFiltration f) (r : ℕ) :
    QuasiCompact (D.stratumι r) := sorry

end DegreeFiltration

/-- A flat, locally finitely presented, separated, quasi-finite scheme morphism admits an
increasing exhaustive closed degree filtration whose strata universally classify finite locally
free base changes and whose canonical inclusions are quasi-compact. -/
theorem exists_degreeFiltration (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f]
    [IsSeparated f] [QuasiFinite f] : Nonempty (DegreeFiltration f) := sorry

end Scheme.Hom
end AlgebraicGeometry
