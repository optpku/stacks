/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.List.TFAE
public import stacks_project.Chap66.Definition_66_9_2_Dimension
public import stacks_project.Chap66.Lemma_66_4_6_Topology
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Lemma_67_27_6_LocallyQuasiFinite
public import stacks_project.Chap68.Lemma_68_12_8_Decent

/-!
# Conditions on a point of an algebraic space locally of finite type over a field

For an algebraic space locally of finite type over a field, a point is closed with
no nontrivial specialization into it if and only if it is isolated, if and only if
the étale-local dimension there vanishes, if and only if the structure morphism is
quasi-finite at that point. If the algebraic space is decent, vanishing of the
local topological Krull dimension of the space of points is equivalent to these.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 68.18.7 (1): Let `X` be an algebraic space locally of finite type over a
field `k`. Let `x : Points X`. Then the following are equivalent: `x` is closed in
`Points X` and the only specialization into `x` is `x` itself; `{x}` is open in
`Points X`; `dimensionAt x = 0`; and the structure morphism `X ⟶ Spec(k)` is
quasi-finite at `x`.

These are source conditions (2), (3), (4), and (5). Isolated points are encoded as
open singletons. The topology on `Points X` is the canonical topology
`instTopologicalSpacePoints`. -/
@[stacks 0AC9]
theorem tfae_isClosed_specializes_isOpen_dimensionAt_quasiFiniteAt {S : Scheme.{u}}
    {X : AlgebraicSpace S} {k : Type u} [Field k] {σ : Spec (.of k) ⟶ S}
    (f : X ⟶ ofOver (Over.mk σ)) [LocallyOfFiniteType f] (x : Points X) :
    List.TFAE
      [ (IsClosed ({x} : Set (Points X)) ∧
          (∀ x' : Points X, Specializes x' x → x' = x))
      , IsOpen ({x} : Set (Points X))
      , dimensionAt x = (0 : WithBot ℕ∞)
      , QuasiFiniteAt f x ] :=
  sorry

/-- Lemma 68.18.7 (2): Let `X` be a decent algebraic space locally of finite type
over a field `k`. Let `x : Points X`. Then `topologicalKrullDimAt x = 0` is
equivalent to `x` being closed in `Points X` with no nontrivial specialization
into `x`, to `{x}` being open, to `dimensionAt x = 0`, and to the structure
morphism `X ⟶ Spec(k)` being quasi-finite at `x`.

This is source condition (1) equivalent to (2)–(5). On a decent algebraic space,
`dimensionAt x = topologicalKrullDimAt x` by Lemma 68.12.5. -/
@[stacks 0AC9]
theorem tfae_topologicalKrullDimAt_isClosed_isOpen_dimensionAt_quasiFiniteAt
    {S : Scheme.{u}} {X : AlgebraicSpace S} {k : Type u} [Field k]
    {σ : Spec (.of k) ⟶ S} (f : X ⟶ ofOver (Over.mk σ)) [LocallyOfFiniteType f]
    [IsDecent X] (x : Points X) :
    List.TFAE
      [ topologicalKrullDimAt x = (0 : WithBot ℕ∞)
      , (IsClosed ({x} : Set (Points X)) ∧
          (∀ x' : Points X, Specializes x' x → x' = x))
      , IsOpen ({x} : Set (Points X))
      , dimensionAt x = (0 : WithBot ℕ∞)
      , QuasiFiniteAt f x ] :=
  sorry

/-- For an algebraic space locally of finite type over a field, a point is closed
with no nontrivial specialization into it if and only if its singleton is open. -/
theorem isClosed_specializes_iff_isOpen_singleton {S : Scheme.{u}}
    {X : AlgebraicSpace S} {k : Type u} [Field k] {σ : Spec (.of k) ⟶ S}
    (f : X ⟶ ofOver (Over.mk σ)) [LocallyOfFiniteType f] (x : Points X) :
    (IsClosed ({x} : Set (Points X)) ∧
        (∀ x' : Points X, Specializes x' x → x' = x)) ↔
      IsOpen ({x} : Set (Points X)) :=
  sorry

/-- For an algebraic space locally of finite type over a field, a point is isolated
if and only if the étale-local dimension there vanishes. -/
theorem isOpen_singleton_iff_dimensionAt_eq_zero {S : Scheme.{u}}
    {X : AlgebraicSpace S} {k : Type u} [Field k] {σ : Spec (.of k) ⟶ S}
    (f : X ⟶ ofOver (Over.mk σ)) [LocallyOfFiniteType f] (x : Points X) :
    IsOpen ({x} : Set (Points X)) ↔ dimensionAt x = (0 : WithBot ℕ∞) :=
  sorry

/-- For an algebraic space locally of finite type over a field, the étale-local
dimension at a point vanishes if and only if the structure morphism is
quasi-finite at that point. -/
theorem dimensionAt_eq_zero_iff_quasiFiniteAt {S : Scheme.{u}}
    {X : AlgebraicSpace S} {k : Type u} [Field k] {σ : Spec (.of k) ⟶ S}
    (f : X ⟶ ofOver (Over.mk σ)) [LocallyOfFiniteType f] (x : Points X) :
    dimensionAt x = (0 : WithBot ℕ∞) ↔ QuasiFiniteAt f x :=
  sorry

/-- For a decent algebraic space locally of finite type over a field, vanishing of
the local topological Krull dimension of the space of points is equivalent to
quasi-finiteness of the structure morphism at that point. -/
theorem topologicalKrullDimAt_eq_zero_iff_quasiFiniteAt {S : Scheme.{u}}
    {X : AlgebraicSpace S} {k : Type u} [Field k] {σ : Spec (.of k) ⟶ S}
    (f : X ⟶ ofOver (Over.mk σ)) [LocallyOfFiniteType f] [IsDecent X]
    (x : Points X) :
    topologicalKrullDimAt x = (0 : WithBot ℕ∞) ↔ QuasiFiniteAt f x :=
  sorry

/-- For a decent algebraic space locally of finite type over a field, vanishing of
the local topological Krull dimension of the space of points is equivalent to
vanishing of the étale-local dimension. -/
theorem topologicalKrullDimAt_eq_zero_iff_dimensionAt_eq_zero {S : Scheme.{u}}
    {X : AlgebraicSpace S} {k : Type u} [Field k] {σ : Spec (.of k) ⟶ S}
    (f : X ⟶ ofOver (Over.mk σ)) [LocallyOfFiniteType f] [IsDecent X]
    (x : Points X) :
    topologicalKrullDimAt x = (0 : WithBot ℕ∞) ↔
      dimensionAt x = (0 : WithBot ℕ∞) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
