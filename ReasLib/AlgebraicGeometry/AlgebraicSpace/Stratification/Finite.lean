/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

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
  rfl

/-- The open stages of a finite filtration built by `ofFiltration` are those of the
supplied filtration. -/
@[simp]
theorem ofFiltration_openStage (F : SchemeStratumFiltration X) (bound : ℕ)
    (pointsSet_last : (F.openStage bound).pointsSet = ∅) :
    (ofFiltration F bound pointsSet_last).openStage = F.openStage :=
  rfl

/-- The presenting schemes of a finite filtration built by `ofFiltration` are those of
the supplied filtration. -/
@[simp]
theorem ofFiltration_schemeStage (F : SchemeStratumFiltration X) (bound : ℕ)
    (pointsSet_last : (F.openStage bound).pointsSet = ∅) :
    (ofFiltration F bound pointsSet_last).schemeStage = F.schemeStage :=
  rfl

/-- The cover morphisms of a finite filtration built by `ofFiltration` are those of
the supplied filtration. -/
@[simp]
theorem ofFiltration_cover (F : SchemeStratumFiltration X) (bound : ℕ)
    (pointsSet_last : (F.openStage bound).pointsSet = ∅) :
    (ofFiltration F bound pointsSet_last).cover = F.cover :=
  rfl

/-- The nested, endpoint, separated, étale, surjective, and isomorphism-over-stratum
conditions of a finite scheme-stratum filtration. -/
theorem spec (F : FiniteSchemeStratumFiltration X) :
    Antitone (fun n ↦ (F.openStage n).pointsSet) ∧
      (F.openStage 0).pointsSet = Set.univ ∧
      (F.openStage F.bound).pointsSet = ∅ ∧
      (∀ n, Scheme.IsSeparated (F.schemeStage n).left) ∧
      (∀ n, Etale (F.cover n)) ∧ (∀ n, Surjective (F.cover n)) ∧
      ∀ n, IsIso (pullback.snd (F.cover n) (reducedStratum F.openStage n).ι) :=
  ⟨F.antitone_pointsSet, F.pointsSet_zero, F.pointsSet_last,
    F.isSeparated_schemeStage, F.etale_cover, F.surjective_cover, F.isIso_cover_stratum⟩

/-- Open stages after the stored bound remain empty. -/
theorem pointsSet_eq_empty_of_le (F : FiniteSchemeStratumFiltration X) {n : ℕ}
    (hn : F.bound ≤ n) : (F.openStage n).pointsSet = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hlast : x ∈ (F.openStage F.bound).pointsSet := F.antitone_pointsSet hn hx
  rw [F.pointsSet_last] at hlast
  exact hlast

/-- The successive reduced differences of a finite scheme-stratum filtration cover `|X|`. -/
theorem iUnion_stratumPoints (F : FiniteSchemeStratumFiltration X) :
    (⋃ n : Fin F.bound, stratumPoints F.openStage n) = Set.univ := by
  classical
  apply Set.eq_univ_of_forall
  intro x
  have hex : ∀ m, x ∈ (F.openStage 0).pointsSet →
      x ∉ (F.openStage m).pointsSet →
      ∃ n : Fin m, x ∈ stratumPoints F.openStage n := by
    intro m
    induction m with
    | zero =>
        intro hx hn
        exact (hn hx).elim
    | succ m ih =>
        intro hx hn
        by_cases hm : x ∈ (F.openStage m).pointsSet
        · exact ⟨⟨m, Nat.lt_succ_self m⟩, hm, hn⟩
        · obtain ⟨n, hn⟩ := ih hx hm
          exact ⟨⟨n.val, Nat.lt_trans n.isLt (Nat.lt_succ_self m)⟩, hn⟩
  apply Set.mem_iUnion.mpr
  apply hex F.bound
  · rw [F.pointsSet_zero]
    exact Set.mem_univ x
  · rw [F.pointsSet_last]
    exact Set.notMem_empty x

/-- Each reduced difference of a finite scheme-stratum filtration is a scheme. -/
theorem isScheme_reducedStratum (F : FiniteSchemeStratumFiltration X) (n : ℕ) :
    IsScheme (reducedStratum F.openStage n).X := by
  let T := reducedStratum F.openStage n
  obtain ⟨V, pV, pT, h⟩ := T.isClosedImmersion.presheaf.1 (F.cover n)
  let p : ofOver V ⟶ T.X := pT
  let q : ofOver V ⟶ ofOver (F.schemeStage n) := yoneda.map pV
  let forget : AlgebraicSpace S ⥤ (Over S)ᵒᵖ ⥤ Type u :=
    { obj := fun Y ↦ Y.functorOfPoints
      map := fun g ↦ g }
  let ff : forget.FullyFaithful := { preimage := fun g ↦ g }
  letI := ff.full
  letI := ff.faithful
  have hp : IsPullback q p (F.cover n) T.ι := by
    apply IsPullback.of_map forget
    · exact h.flip.w
    · exact h.flip
  letI : IsIso (pullback.snd (F.cover n) T.ι) := F.isIso_cover_stratum n
  haveI : IsIso p := by
    rw [← hp.isoPullback_hom_snd]
    infer_instance
  exact IsScheme.of (asIso p).symm

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
        ∀ i, IsScheme (reducedStratum U i).X := by
  obtain ⟨F⟩ := exists_finiteSchemeStratumFiltration X
  exact ⟨F.bound, F.openStage, F.antitone_pointsSet, F.pointsSet_zero,
    F.pointsSet_last, F.isScheme_reducedStratum⟩

end AlgebraicGeometry.AlgebraicSpace
