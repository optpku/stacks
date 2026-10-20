module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Stratification
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Reasonable
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IsScheme

/-!
# Finite nested open filtrations of reasonable algebraic spaces by scheme strata

Terminating nested open subspaces of an algebraic space carry
separated-scheme surjective étale presentations
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
successive reduced differences. Stages are indexed from zero, and the stage at
the stored bound is empty. -/
structure FiniteSchemeStratumFiltration (X : AlgebraicSpace S) extends
    SchemeStratumFiltration X where
  /-- A terminating index in the zero-based sequence of open stages. -/
  bound : ℕ
  /-- The open stage at the stored bound has empty support. -/
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

/-- Each reduced difference of a finite scheme-stratum filtration is a scheme. -/
theorem isScheme_reducedStratum (F : FiniteSchemeStratumFiltration X) (n : ℕ) :
    IsScheme (reducedStratum F.openStage n).X :=
  sorry

end FiniteSchemeStratumFiltration

/-- A quasi-compact reasonable algebraic space admits a finite nested open filtration
by scheme strata with separated-scheme surjective étale presentations isomorphic over
the reduced differences. -/
theorem exists_finiteSchemeStratumFiltration (X : AlgebraicSpace S) [IsQuasiCompact X]
    [IsReasonable X] : Nonempty (FiniteSchemeStratumFiltration X) :=
  sorry

/-- A quasi-compact reasonable algebraic space admits a finite nested open
filtration whose successive reduced differences are schemes. -/
theorem exists_openFiltration_reducedStratum_isScheme (X : AlgebraicSpace S)
    [IsQuasiCompact X] [IsReasonable X] :
    ∃ (n : ℕ) (U : ℕ → OpenSubspace X),
      Antitone (fun i ↦ (U i).pointsSet) ∧
        (U 0).pointsSet = Set.univ ∧
        (U n).pointsSet = ∅ ∧
        ∀ i, IsScheme (reducedStratum U i).X :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
