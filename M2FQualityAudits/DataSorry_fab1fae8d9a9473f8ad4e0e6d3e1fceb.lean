module

import Lean

public import Mathlib.Data.Finite.Defs
public import Mathlib.Data.List.TFAE
public import Mathlib.Topology.Order
public import stacks_project.Chap66.Definition_66_9_2_Dimension
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
`topologicalKrullDim (Points X) = 0`, `dimension X = 0`, and the structure
morphism `X ⟶ Spec(k)` is locally quasi-finite.

The topology on `Points X` is the open-quotient étale topology of an atlas
`A : Points.OpenQuotientAtlas X τ`. The source also lists finiteness of
`Points X` as condition (1); that condition is not equivalent to the others. -/
@[stacks 0ACA]
theorem tfae_discrete_dimension_locallyQuasiFinite {S : Scheme.{u}}
    {X : AlgebraicSpace S} {k : Type u} [Field k] {σ : Spec (.of k) ⟶ S}
    (f : X ⟶ ofOver (Over.mk σ)) [LocallyOfFiniteType f]
    (τ : TopologicalSpace (Points X)) (A : Points.OpenQuotientAtlas X τ) :
    List.TFAE
      [ @DiscreteTopology (Points X) τ
      , @topologicalKrullDim (Points X) τ = 0
      , dimension X = 0
      , LocallyQuasiFinite f ] :=
  sorry

/-- Lemma 68.18.8 (2): Let `X` be a decent algebraic space locally of finite type
over a field `k`. If `Points X` is finite, then the structure morphism
`X ⟶ Spec(k)` is locally quasi-finite. -/
@[stacks 0ACA]
instance locallyQuasiFinite_of_isDecent_finite {S : Scheme.{u}}
    {X : AlgebraicSpace S} {k : Type u} [Field k] {σ : Spec (.of k) ⟶ S}
    (f : X ⟶ ofOver (Over.mk σ)) [LocallyOfFiniteType f] [IsDecent X]
    [Finite (Points X)] : LocallyQuasiFinite f :=
  sorry

/-- For an algebraic space locally of finite type over a field, the space of
points is discrete if and only if its topological Krull dimension is `0`. -/
theorem discreteTopology_iff_topologicalKrullDim_eq_zero {S : Scheme.{u}}
    {X : AlgebraicSpace S} {k : Type u} [Field k] {σ : Spec (.of k) ⟶ S}
    (f : X ⟶ ofOver (Over.mk σ)) [LocallyOfFiniteType f]
    (τ : TopologicalSpace (Points X)) (A : Points.OpenQuotientAtlas X τ) :
    @DiscreteTopology (Points X) τ ↔ @topologicalKrullDim (Points X) τ = 0 :=
  sorry

/-- For an algebraic space locally of finite type over a field, the topological
Krull dimension of the space of points vanishes if and only if the étale-local
dimension of `X` vanishes. -/
theorem topologicalKrullDim_eq_zero_iff_dimension_eq_zero {S : Scheme.{u}}
    {X : AlgebraicSpace S} {k : Type u} [Field k] {σ : Spec (.of k) ⟶ S}
    (f : X ⟶ ofOver (Over.mk σ)) [LocallyOfFiniteType f]
    (τ : TopologicalSpace (Points X)) (A : Points.OpenQuotientAtlas X τ) :
    @topologicalKrullDim (Points X) τ = 0 ↔ dimension X = 0 :=
  sorry

/-- For an algebraic space locally of finite type over a field, the étale-local
dimension of `X` vanishes if and only if the structure morphism is locally
quasi-finite. -/
theorem dimension_eq_zero_iff_locallyQuasiFinite {S : Scheme.{u}}
    {X : AlgebraicSpace S} {k : Type u} [Field k] {σ : Spec (.of k) ⟶ S}
    (f : X ⟶ ofOver (Over.mk σ)) [LocallyOfFiniteType f] :
    dimension X = 0 ↔ LocallyQuasiFinite f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace


namespace M2FDataSorryAudit

open Lean Meta Elab Command

private def containsNonPropSorry (value : Expr) : MetaM Bool := do
  let found ← IO.mkRef false
  forEachExpr value fun expr => do
    unless ← found.get do
      let (head, args) := expr.getAppFnArgs
      if head == ``sorryAx && args.size >= 1 then
        unless ← isProp args[0]! do
          found.set true
  found.get

run_cmd do
  let env ← getEnv
  -- `env.constants` also contains imported declarations.  Current-module
  -- declarations are the ones without a `const2ModIdx` entry; restricting the
  -- scan to them is important for remote compilation because `mkModuleData`
  -- materializes and traverses the entire imported environment.  That made a
  -- tiny audit scratch file hit Leanfra's cancellation deadline on large repos.
  for (name, info) in env.constants do
    if (Environment.getModuleIdxFor? env name).isNone then
      if let some value := info.value? true then
        let (hasNonPropSorry, _) ← liftCoreM <| (containsNonPropSorry value).run
        if hasNonPropSorry then
          logInfo m!"M2F_NON_PROP_DATA_SORRY|{privateToUserName name}"

end M2FDataSorryAudit
