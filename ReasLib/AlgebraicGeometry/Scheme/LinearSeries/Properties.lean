/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.LinearSystem.Separation
public import ReasLib.AlgebraicGeometry.Scheme.LinearSeries

/-!
# Properties of linear series

Completeness, generation, and the closed-immersion property of a linear series.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.ProjectiveSpace.VectorSpace.LinearSystem
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.LinearSeries

/-- A linear series is complete exactly when its chosen section subspace is the full space of sections. -/
def IsComplete {k : Type u} [Field k] {X : SchemeOverField k} [IsProper X.hom]
    {hdim : topologicalKrullDim X.left ≤ 1} {d r : ℕ}
    (g : LinearSeries X hdim d r) : Prop :=
  g.sections = ⊤

/-- Completeness is equivalent to equality with the full section space. -/
theorem isComplete_iff {k : Type u} [Field k] {X : SchemeOverField k}
    [IsProper X.hom] {hdim : topologicalKrullDim X.left ≤ 1} {d r : ℕ}
    (g : LinearSeries X hdim d r) :
    IsComplete g ↔ g.sections = ⊤ := sorry

/-- A linear series is base-point-free when its section inclusion generates the line bundle. -/
def IsBasePointFree {k : Type u} [Field k] {X : SchemeOverField k}
    [IsProper X.hom] {hdim : topologicalKrullDim X.left ≤ 1} {d r : ℕ}
    (g : LinearSeries X hdim d r) : Prop :=
  Generates X g.lineBundle g.inclusion

/-- Base-point-freeness is equivalent to generation by the section inclusion. -/
theorem isBasePointFree_iff {k : Type u} [Field k] {X : SchemeOverField k}
    [IsProper X.hom] {hdim : topologicalKrullDim X.left ≤ 1} {d r : ℕ}
    (g : LinearSeries X hdim d r) :
    IsBasePointFree g ↔ Generates X g.lineBundle g.inclusion := sorry

/-- A linear series induces a closed embedding when its section inclusion induces a closed immersion. -/
def InducesClosedEmbedding {k : Type u} [Field k] {X : SchemeOverField k}
    [IsProper X.hom] {hdim : topologicalKrullDim X.left ≤ 1} {d r : ℕ}
    (g : LinearSeries X hdim d r) : Prop :=
  @InducesClosedImmersion k _ g.sections _ _ X g.lineBundle g.isInvertible g.inclusion

/-- Closed-embedding induction is equivalent to the corresponding closed-immersion property. -/
theorem inducesClosedEmbedding_iff {k : Type u} [Field k] {X : SchemeOverField k}
    [IsProper X.hom] {hdim : topologicalKrullDim X.left ≤ 1} {d r : ℕ}
    (g : LinearSeries X hdim d r) :
    InducesClosedEmbedding g ↔
      @InducesClosedImmersion k _ g.sections _ _ X g.lineBundle g.isInvertible
        g.inclusion := sorry

end AlgebraicGeometry.LinearSeries
