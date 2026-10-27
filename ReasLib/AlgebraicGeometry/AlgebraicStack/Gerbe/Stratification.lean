/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.Countable.Defs
public import Mathlib.Order.Hom.Basic
public import Mathlib.Order.RelClasses
public import Mathlib.SetTheory.Cardinal.Order
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Substack.LocallyClosed
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Substack.Opens
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Substack.Points
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Gerbe
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Reduced
public import ReasLib.AlgebraicGeometry.AlgebraicStack.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Morphism.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Inertia

/-!
# Well-ordered stratifications by gerbes

Successive closed remainders support reduced locally closed gerbe strata.
Dense maximal strata determine a canonical stratification up to order isomorphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids (toFunctor)
open FiberedCategoryOver.Groupoids.Inertia (forget)
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.GerbeStratification

variable {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]

section Remainders

variable {I : Type (u + 1)} [LinearOrder I]

/-- The remainder at an index is the complement of the point images of all earlier strata. -/
def remainder (U : I → Substack.LocallyClosed X) (i : I) : Set (Points X) :=
  (Set.univ : Set (Points X)) \ ⋃ i', ⋃ (_ : i' < i), (U i').pointsSet

/-- The remainder is the complement in the ambient point space of the union of earlier strata. -/
theorem remainder_def (U : I → Substack.LocallyClosed X) (i : I) :
    remainder U i =
      (Set.univ : Set (Points X)) \ ⋃ i', ⋃ (_ : i' < i), (U i').pointsSet := sorry

/-- A point belongs to a remainder exactly when it belongs to none of the earlier strata. -/
theorem mem_remainder (U : I → Substack.LocallyClosed X) {i : I} {x : Points X} :
    x ∈ remainder U i ↔ ∀ i' < i, x ∉ (U i').pointsSet := sorry

/-- A gerbe stratification consists of nonempty reduced gerbe strata covering the point
space, each contained and relatively open in its closed successive remainder. -/
def IsStratification (U : I → Substack.LocallyClosed X) : Prop :=
  (∀ i, IsReduced (U i).category) ∧ (∀ i, IsGerbe (U i).category) ∧
    (∀ i, (U i).pointsSet.Nonempty) ∧
    (⋃ i, (U i).pointsSet) = Set.univ ∧
    (∀ i, IsClosed (remainder U i)) ∧
    (∀ i, (U i).pointsSet ⊆ remainder U i) ∧
    (∀ i, ∃ O : Set (Points X), IsOpen O ∧
      O ∩ remainder U i = (U i).pointsSet)

end Remainders

/-- A maximal dense gerbe stratification is a gerbe stratification dense in every
remainder, whose strata are the largest open gerbes in the reduced closed substacks
on those remainders, identified both by essential images and by point images. -/
def IsMaximalDense {I : Type (u + 1)} [LinearOrder I] [WellFoundedLT I]
    (U : I → Substack.LocallyClosed X) : Prop :=
  IsStratification U ∧
    (∀ i, remainder U i ⊆ closure (U i).pointsSet) ∧
    (∀ i, ∃ (Z : Substack.Closed X)
        (W : Substack.Open (Substack.closedCategory X Z.val Z.property)),
      Substack.pointsSet X Z.val Z.property = remainder U i ∧
        IsReduced (Substack.closedCategory X Z.val Z.property) ∧
        IsGerbe W.category ∧ Dense W.pointsSet ∧
        (∀ W' : Substack.Open (Substack.closedCategory X Z.val Z.property),
          IsGerbe W'.category → W'.pointsSet ⊆ W.pointsSet) ∧
        (U i).val =
          (toFunctor (W.inclusion ≫ Substack.closedInclusion X Z.val Z.property)).essImage ∧
        (U i).pointsSet = Set.range
          (Points.map (W.inclusion ≫ Substack.closedInclusion X Z.val Z.property)))

/-- Maximal dense stratifications satisfy precisely the covering, remainder, density,
and largest-open-gerbe conditions on their canonical substacks. -/
theorem isMaximalDense_iff {I : Type (u + 1)} [LinearOrder I] [WellFoundedLT I]
    (U : I → Substack.LocallyClosed X) :
    IsMaximalDense U ↔
      (∀ i, IsReduced (U i).category) ∧ (∀ i, IsGerbe (U i).category) ∧
        (∀ i, (U i).pointsSet.Nonempty) ∧
        (⋃ i, (U i).pointsSet) = Set.univ ∧
        (∀ i, IsClosed (remainder U i)) ∧
        (∀ i, (U i).pointsSet ⊆ remainder U i) ∧
        (∀ i, ∃ O : Set (Points X), IsOpen O ∧
          O ∩ remainder U i = (U i).pointsSet) ∧
        (∀ i, remainder U i ⊆ closure (U i).pointsSet) ∧
        (∀ i, ∃ (Z : Substack.Closed X)
            (W : Substack.Open (Substack.closedCategory X Z.val Z.property)),
          Substack.pointsSet X Z.val Z.property = remainder U i ∧
            IsReduced (Substack.closedCategory X Z.val Z.property) ∧
            IsGerbe W.category ∧ Dense W.pointsSet ∧
            (∀ W' : Substack.Open (Substack.closedCategory X Z.val Z.property),
              IsGerbe W'.category → W'.pointsSet ⊆ W.pointsSet) ∧
            (U i).val =
              (toFunctor (W.inclusion ≫ Substack.closedInclusion X Z.val Z.property)).essImage ∧
            (U i).pointsSet = Set.range
              (Points.map (W.inclusion ≫ Substack.closedInclusion X Z.val Z.property))) := sorry

/-- An algebraic stack with quasi-compact inertia admits a well-ordered gerbe
stratification dense in every successive remainder. -/
theorem exists_dense {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] [QuasiCompact (forget.{u + 1, u, u, u + 1} X)] :
    ∃ (I : Type (u + 1)) (_ : LinearOrder I) (_ : WellFoundedLT I)
      (U : I → Substack.LocallyClosed X),
      IsStratification U ∧ (∀ i, remainder U i ⊆ closure (U i).pointsSet) := sorry

/-- An algebraic stack with quasi-compact inertia admits a well-ordered gerbe
stratification whose strata are quasi-compact. -/
theorem exists_quasiCompact {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] [QuasiCompact (forget.{u + 1, u, u, u + 1} X)] :
    ∃ (I : Type (u + 1)) (_ : LinearOrder I) (_ : WellFoundedLT I)
      (U : I → Substack.LocallyClosed X),
      IsStratification U ∧ (∀ i, IsQuasiCompact (U i).category) := sorry

/-- An algebraic stack with quasi-compact inertia admits a well-ordered maximal
dense gerbe stratification. -/
theorem exists_maximal_dense {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] [QuasiCompact (forget.{u + 1, u, u, u + 1} X)] :
    ∃ (I : Type (u + 1)) (_ : LinearOrder I) (_ : WellFoundedLT I)
      (U : I → Substack.LocallyClosed X), IsMaximalDense U := sorry

/-- Two maximal dense gerbe stratifications of an algebraic stack with quasi-compact
inertia agree on their object properties along an order isomorphism of their indices. -/
theorem unique_maximal_dense {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] [QuasiCompact (forget.{u + 1, u, u, u + 1} X)]
    {I J : Type (u + 1)}
    [LinearOrder I] [WellFoundedLT I] [LinearOrder J] [WellFoundedLT J]
    (U : I → Substack.LocallyClosed X) (V : J → Substack.LocallyClosed X)
    (hU : IsMaximalDense U) (hV : IsMaximalDense V) :
    ∃ e : I ≃o J, ∀ i, (U i).val = (V (e i)).val := sorry

/-- The proposition that every maximal dense gerbe stratification of an algebraic
stack with quasi-compact inertia has a countable index. -/
def countableIndex {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] [QuasiCompact (forget.{u + 1, u, u, u + 1} X)] : Prop :=
  ∀ {I : Type (u + 1)} [LinearOrder I] [WellFoundedLT I]
    (U : I → Substack.LocallyClosed X), IsMaximalDense U → Countable I

/-- The countable-index proposition quantifies over all well-ordered maximal dense
gerbe stratifications of the stack. -/
theorem countableIndex_iff {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] [QuasiCompact (forget.{u + 1, u, u, u + 1} X)] :
    countableIndex X ↔
      ∀ {I : Type (u + 1)} [LinearOrder I] [WellFoundedLT I]
        (U : I → Substack.LocallyClosed X), IsMaximalDense U → Countable I := sorry

/-- The countable-index proposition is equivalent to bounding the cardinal of each
maximal dense gerbe stratification index by `Cardinal.aleph0`. -/
theorem countableIndex_iff_mk_le_aleph0 {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] [QuasiCompact (forget.{u + 1, u, u, u + 1} X)] :
    countableIndex X ↔
      ∀ {I : Type (u + 1)} [LinearOrder I] [WellFoundedLT I]
        (U : I → Substack.LocallyClosed X),
        IsMaximalDense U → Cardinal.mk I ≤ Cardinal.aleph0 := sorry

end AlgebraicGeometry.AlgebraicStack.GerbeStratification
