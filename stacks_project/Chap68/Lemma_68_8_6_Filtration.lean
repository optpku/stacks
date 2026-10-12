/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap68.Lemma_68_8_4_Filtration
public import stacks_project.Chap66.Definition_66_3_1_Separation

/-!
# Finite nested open filtrations of qcqs algebraic spaces by scheme strata

This file owns terminating nested open subspaces of a quasi-compact absolutely
quasi-separated algebraic space together with quasi-compact separated-scheme
surjective étale presentations that are isomorphisms over the successive
reduced differences.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- A terminating nested sequence of open subspaces of `X` equipped with
quasi-compact separated-scheme surjective étale presentations that are
isomorphisms over the successive reduced differences. The stored bound encodes
source `U_{n+1} = ∅`, and quasi-compactness of each presenting scheme `V_p` is
the qcqs refinement of `FiniteSchemeStratumFiltration`. -/
structure QuasiCompactFiniteSchemeStratumFiltration (X : AlgebraicSpace S) extends
    FiniteSchemeStratumFiltration X where
  /-- Each presenting scheme `V_{n+1}` is quasi-compact. -/
  isQuasiCompact_schemeStage (n : ℕ) : CompactSpace (schemeStage n).left

namespace QuasiCompactFiniteSchemeStratumFiltration

/-- Convert a finite scheme-stratum filtration whose presenting schemes are
quasi-compact into a qcqs scheme-stratum filtration. -/
def ofFiltration (F : FiniteSchemeStratumFiltration X)
    (isQuasiCompact_schemeStage : ∀ n, CompactSpace (F.schemeStage n).left) :
    QuasiCompactFiniteSchemeStratumFiltration X where
  toFiniteSchemeStratumFiltration := F
  isQuasiCompact_schemeStage := isQuasiCompact_schemeStage

/-- The bound of a qcqs filtration built by `ofFiltration` is that of the supplied
finite filtration. -/
@[simp]
theorem ofFiltration_bound (F : FiniteSchemeStratumFiltration X)
    (isQuasiCompact_schemeStage : ∀ n, CompactSpace (F.schemeStage n).left) :
    (ofFiltration F isQuasiCompact_schemeStage).bound = F.bound :=
  sorry

/-- The open stages of a qcqs filtration built by `ofFiltration` are those of the
supplied finite filtration. -/
@[simp]
theorem ofFiltration_openStage (F : FiniteSchemeStratumFiltration X)
    (isQuasiCompact_schemeStage : ∀ n, CompactSpace (F.schemeStage n).left) :
    (ofFiltration F isQuasiCompact_schemeStage).openStage = F.openStage :=
  sorry

/-- The presenting schemes of a qcqs filtration built by `ofFiltration` are those of
the supplied finite filtration. -/
@[simp]
theorem ofFiltration_schemeStage (F : FiniteSchemeStratumFiltration X)
    (isQuasiCompact_schemeStage : ∀ n, CompactSpace (F.schemeStage n).left) :
    (ofFiltration F isQuasiCompact_schemeStage).schemeStage = F.schemeStage :=
  sorry

/-- The cover morphisms of a qcqs filtration built by `ofFiltration` are those of
the supplied finite filtration. -/
@[simp]
theorem ofFiltration_cover (F : FiniteSchemeStratumFiltration X)
    (isQuasiCompact_schemeStage : ∀ n, CompactSpace (F.schemeStage n).left) :
    (ofFiltration F isQuasiCompact_schemeStage).cover = F.cover :=
  sorry

/-- The nested, endpoint, quasi-compact, separated, étale, surjective, and
isomorphism-over-stratum conditions of a qcqs scheme-stratum filtration. -/
theorem spec (F : QuasiCompactFiniteSchemeStratumFiltration X) :
    Antitone (fun n ↦ (F.openStage n).pointsSet) ∧
      (F.openStage 0).pointsSet = Set.univ ∧
      (F.openStage F.bound).pointsSet = ∅ ∧
      (∀ n, CompactSpace (F.schemeStage n).left) ∧
      (∀ n, Scheme.IsSeparated (F.schemeStage n).left) ∧
      (∀ n, Etale (F.cover n)) ∧ (∀ n, Surjective (F.cover n)) ∧
      ∀ n, IsIso (pullback.snd (F.cover n) (reducedStratum F.openStage n).ι) :=
  sorry

end QuasiCompactFiniteSchemeStratumFiltration

/-- A quasi-compact absolutely quasi-separated algebraic space admits a finite
nested open filtration by scheme strata with quasi-compact separated-scheme
surjective étale presentations isomorphic over the reduced differences. -/
theorem exists_quasiCompactFiniteSchemeStratumFiltration (X : AlgebraicSpace S)
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X] :
    Nonempty (QuasiCompactFiniteSchemeStratumFiltration X) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
