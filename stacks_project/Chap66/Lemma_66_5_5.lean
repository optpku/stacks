/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.Spectral.Prespectral
public import stacks_project.Chap66.Lemma_66_5_5_PointsTopology

/-!
# Local quasi-compactness of algebraic spaces

Every point of `|X|` has a fundamental system of open quasi-compact neighbourhoods.
In particular `|X|` is locally quasi-compact in the sense of Topology, Definition 5.13.1.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Points

/-- Lemma 66.5.5 (1): let `S` be a scheme. Let `X` be an algebraic space over `S`.
Every point of `|X|` has a fundamental system of open quasi-compact neighbourhoods. -/
@[stacks 04NN]
theorem prespectralSpace {S : Scheme.{u}} (X : AlgebraicSpace S)
    (τ : TopologicalSpace (Points X)) (A : OpenQuotientAtlas X τ) :
    @PrespectralSpace (Points X) τ :=
  sorry

/-- Lemma 66.5.5 (2): in particular `|X|` is locally quasi-compact in the sense of
Topology, Definition 5.13.1. -/
@[stacks 04NN]
theorem locallyCompactSpace {S : Scheme.{u}} (X : AlgebraicSpace S)
    (τ : TopologicalSpace (Points X)) (A : OpenQuotientAtlas X τ) :
    @LocallyCompactSpace (Points X) τ :=
  sorry

/-- Every point of `|X|` has a fundamental system of open quasi-compact neighbourhoods. -/
theorem exists_isOpen_isCompact_mem_nhds {S : Scheme.{u}} (X : AlgebraicSpace S)
    (τ : TopologicalSpace (Points X)) (A : OpenQuotientAtlas X τ) (x : Points X)
    (n : Set (Points X)) (hn : n ∈ @nhds (Points X) τ x) :
    ∃ s : Set (Points X),
      @IsOpen (Points X) τ s ∧ @IsCompact (Points X) τ s ∧ x ∈ s ∧ s ⊆ n :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Points
