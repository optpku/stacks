/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.Finite.Defs
public import Mathlib.Data.List.TFAE
public import stacks_project.Chap66.Definition_66_9_2_Dimension
public import stacks_project.Chap66.Lemma_66_4_6_Topology
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Lemma_67_27_7_LocallyQuasiFinite
public import stacks_project.Chap68.Lemma_68_12_8_Decent

/-!
# Conditions on an algebraic space locally of finite type over a field

For an algebraic space locally of finite type over a field, discreteness of the
space of points, vanishing of its topological Krull dimension, vanishing of the
étale-local dimension, and local quasi-finiteness of the structure morphism are
equivalent. If the algebraic space is decent, finiteness of the space of points
implies these conditions.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 68.18.8 (1): Let `X` be an algebraic space locally of finite type over a
field `k`. Then the following are equivalent: `Points X` is a discrete space,
`topologicalKrullDim (Points X) ≤ 0`, `dimension X ≤ 0`, and the structure
morphism `X ⟶ Spec(k)` is locally quasi-finite.

The topology on `Points X` is the canonical topology `instTopologicalSpacePoints`.
The source writes `dim(|X|) = 0` and `dim(X) = 0`; the Lean statements use `≤ 0`
so that the empty algebraic space, whose dimensions are `⊥`, is included. The
source also lists finiteness of `Points X` as condition (1); that condition is
not equivalent to the others. -/
@[stacks 0ACA]
theorem tfae_discrete_dimension_locallyQuasiFinite {S : Scheme.{u}}
    {X : AlgebraicSpace S} {k : Type u} [Field k] {σ : Spec (.of k) ⟶ S}
    (f : X ⟶ ofOver (Over.mk σ)) [LocallyOfFiniteType f] :
    List.TFAE
      [ DiscreteTopology (Points X)
      , topologicalKrullDim (Points X) ≤ 0
      , dimension X ≤ 0
      , LocallyQuasiFinite f ] :=
  sorry

/-- Lemma 68.18.8 (2): Let `X` be a decent algebraic space locally of finite type
over a field `k`. If `Points X` is finite, then the structure morphism
`X ⟶ Spec(k)` is locally quasi-finite.

The source writes this as (1) implying the equivalent conditions of
Lemma 68.18.8 (1), including `dim(|X|) = 0` and `dim(X) = 0`. Those dimension
conditions are read as `≤ 0` so the empty space (dimension `⊥`) is included. -/
@[stacks 0ACA]
instance locallyQuasiFinite_of_isDecent_finite {S : Scheme.{u}}
    {X : AlgebraicSpace S} {k : Type u} [Field k] {σ : Spec (.of k) ⟶ S}
    (f : X ⟶ ofOver (Over.mk σ)) [LocallyOfFiniteType f] [IsDecent X]
    [Finite (Points X)] : LocallyQuasiFinite f :=
  sorry

/-- For a decent algebraic space locally of finite type over a field, finiteness of
the space of points implies that this space is discrete. -/
theorem discreteTopology_of_isDecent_finite {S : Scheme.{u}}
    {X : AlgebraicSpace S} {k : Type u} [Field k] {σ : Spec (.of k) ⟶ S}
    (f : X ⟶ ofOver (Over.mk σ)) [LocallyOfFiniteType f] [IsDecent X]
    [Finite (Points X)] : DiscreteTopology (Points X) :=
  sorry

/-- For an algebraic space locally of finite type over a field, the space of
points is discrete if and only if its topological Krull dimension is at most
`0`. The source writes equality with `0`; `≤ 0` includes the empty space, whose
dimension is `⊥`. -/
theorem discreteTopology_iff_topologicalKrullDim_le_zero {S : Scheme.{u}}
    {X : AlgebraicSpace S} {k : Type u} [Field k] {σ : Spec (.of k) ⟶ S}
    (f : X ⟶ ofOver (Over.mk σ)) [LocallyOfFiniteType f] :
    DiscreteTopology (Points X) ↔ topologicalKrullDim (Points X) ≤ 0 :=
  sorry

/-- For an algebraic space locally of finite type over a field, the topological
Krull dimension of the space of points is at most `0` if and only if the
étale-local dimension of `X` is at most `0`. The source writes equality with
`0`; `≤ 0` includes the empty space, whose dimension is `⊥`. -/
theorem topologicalKrullDim_le_zero_iff_dimension_le_zero {S : Scheme.{u}}
    {X : AlgebraicSpace S} {k : Type u} [Field k] {σ : Spec (.of k) ⟶ S}
    (f : X ⟶ ofOver (Over.mk σ)) [LocallyOfFiniteType f] :
    topologicalKrullDim (Points X) ≤ 0 ↔ dimension X ≤ 0 :=
  sorry

/-- For an algebraic space locally of finite type over a field, the étale-local
dimension of `X` is at most `0` if and only if the structure morphism is locally
quasi-finite. The source writes equality with `0`; `≤ 0` includes the empty
space, whose dimension is `⊥`. -/
theorem dimension_le_zero_iff_locallyQuasiFinite {S : Scheme.{u}}
    {X : AlgebraicSpace S} {k : Type u} [Field k] {σ : Spec (.of k) ⟶ S}
    (f : X ⟶ ofOver (Over.mk σ)) [LocallyOfFiniteType f] :
    dimension X ≤ 0 ↔ LocallyQuasiFinite f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
