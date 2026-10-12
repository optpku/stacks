/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap68.Lemma_68_8_3_Filtration
public import stacks_project.Chap68.Lemma_68_17_4_Relative

/-!
# Finite nested open filtrations of reasonable algebraic spaces by scheme strata

This file owns terminating nested open subspaces of a quasi-compact reasonable
algebraic space together with separated-scheme surjective étale presentations
that are isomorphisms over the successive reduced differences.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- A terminating nested sequence of open subspaces of `X` equipped with
separated-scheme surjective étale presentations that are isomorphisms over the
successive reduced differences. The stored bound encodes source `U_{n+1} = ∅`. -/
structure FiniteSchemeStratumFiltration (X : AlgebraicSpace S) extends
    SchemeStratumFiltration X where
  /-- An index `n` such that `openStage n` is empty, corresponding to source `U_{n+1} = ∅`. -/
  bound : ℕ
  /-- The last open stage occupies none of `|X|`, encoding `U_{n+1} = ∅`. -/
  pointsSet_last : (openStage bound).pointsSet = ∅

namespace FiniteSchemeStratumFiltration

/-- Convert a scheme-stratum filtration together with a terminating index into a
finite scheme-stratum filtration. -/
def ofFiltration (F : SchemeStratumFiltration X) (bound : ℕ)
    (pointsSet_last : (F.openStage bound).pointsSet = ∅) :
    FiniteSchemeStratumFiltration X where
  toSchemeStratumFiltration := F
  bound := bound
  pointsSet_last := pointsSet_last

/-- The bound of a finite filtration built by `ofFiltration` is the supplied bound. -/
@[simp]
theorem ofFiltration_bound (F : SchemeStratumFiltration X) (bound : ℕ)
    (pointsSet_last : (F.openStage bound).pointsSet = ∅) :
    (ofFiltration F bound pointsSet_last).bound = bound :=
  sorry

/-- The open stages of a finite filtration built by `ofFiltration` are those of the
supplied filtration. -/
@[simp]
theorem ofFiltration_openStage (F : SchemeStratumFiltration X) (bound : ℕ)
    (pointsSet_last : (F.openStage bound).pointsSet = ∅) :
    (ofFiltration F bound pointsSet_last).openStage = F.openStage :=
  sorry

/-- The presenting schemes of a finite filtration built by `ofFiltration` are those of
the supplied filtration. -/
@[simp]
theorem ofFiltration_schemeStage (F : SchemeStratumFiltration X) (bound : ℕ)
    (pointsSet_last : (F.openStage bound).pointsSet = ∅) :
    (ofFiltration F bound pointsSet_last).schemeStage = F.schemeStage :=
  sorry

/-- The cover morphisms of a finite filtration built by `ofFiltration` are those of
the supplied filtration. -/
@[simp]
theorem ofFiltration_cover (F : SchemeStratumFiltration X) (bound : ℕ)
    (pointsSet_last : (F.openStage bound).pointsSet = ∅) :
    (ofFiltration F bound pointsSet_last).cover = F.cover :=
  sorry

/-- The nested, endpoint, separated, étale, surjective, and isomorphism-over-stratum
conditions of a finite scheme-stratum filtration. -/
theorem spec (F : FiniteSchemeStratumFiltration X) :
    Antitone (fun n ↦ (F.openStage n).pointsSet) ∧
      (F.openStage 0).pointsSet = Set.univ ∧
      (F.openStage F.bound).pointsSet = ∅ ∧
      (∀ n, Scheme.IsSeparated (F.schemeStage n).left) ∧
      (∀ n, Etale (F.cover n)) ∧ (∀ n, Surjective (F.cover n)) ∧
      ∀ n, IsIso (pullback.snd (F.cover n) (reducedStratum F.openStage n).ι) :=
  sorry

/-- Open stages after the stored bound remain empty. -/
theorem pointsSet_eq_empty_of_le (F : FiniteSchemeStratumFiltration X) {n : ℕ}
    (hn : F.bound ≤ n) : (F.openStage n).pointsSet = ∅ :=
  sorry

/-- The successive reduced differences of a finite scheme-stratum filtration cover `|X|`. -/
theorem iUnion_stratumPoints (F : FiniteSchemeStratumFiltration X) :
    (⋃ n : Fin F.bound, stratumPoints F.openStage n) = Set.univ :=
  sorry

end FiniteSchemeStratumFiltration

/-- A quasi-compact reasonable algebraic space admits a finite nested open filtration
by scheme strata with separated-scheme surjective étale presentations isomorphic over
the reduced differences. -/
theorem exists_finiteSchemeStratumFiltration (X : AlgebraicSpace S) [IsQuasiCompact X]
    [IsReasonable X] : Nonempty (FiniteSchemeStratumFiltration X) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
