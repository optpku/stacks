/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.Spectral.Prespectral
public import stacks_project.Chap100.Lemma_100_4_7_Topology

/-!
# Local quasi-compactness of algebraic stacks

Every point of `|X|` has a fundamental system of quasi-compact open neighbourhoods.
In particular `|X|` is locally quasi-compact in the sense of Topology, Definition 5.13.1.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Topology

open scoped Bicategory Topology

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Lemma 100.4.9 (1): let `S` be a scheme. Let `X` be an algebraic stack over `S`.
Every point of `|X|` has a fundamental system of quasi-compact open neighbourhoods. -/
@[stacks 04Y9, instance]
instance instPrespectralSpacePoints {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] : PrespectralSpace (Points X) :=
  sorry

/-- Lemma 100.4.9 (2): in particular `|X|` is locally quasi-compact in the sense of
Topology, Definition 5.13.1. -/
@[stacks 04Y9, instance]
instance instLocallyCompactSpacePoints {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] : LocallyCompactSpace (Points X) :=
  sorry

namespace Points

/-- Every point of `|X|` has a fundamental system of quasi-compact open neighbourhoods. -/
theorem exists_isOpen_isCompact_mem_nhds {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] (x : Points X) (n : Set (Points X)) (hn : n ∈ 𝓝 x) :
    ∃ s : Set (Points X), IsOpen s ∧ IsCompact s ∧ x ∈ s ∧ s ⊆ n :=
  sorry

end Points

end AlgebraicGeometry.AlgebraicStack
