/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.Countable.Defs
public import Mathlib.SetTheory.Cardinal.Order
public import stacks_project.Chap101.Lemma_101_29_3

/-!
# Cardinality of canonical dense gerbe stratifications

Lemma 101.29.3 produces a maximal dense type-(a) gerbe stratification of an
algebraic stack with quasi-compact inertia, unique up to order isomorphism of
the well-ordered index. Whether that index is countable is left open.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids.Inertia (forget)
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.GerbeStratification

/-- A well-ordered family of locally closed substacks is a maximal dense
type-(a) gerbe stratification when each stratum is a nonempty reduced gerbe,
the images of points cover `|X|`, remainders are closed, each `|U i|` is open
and dense in its remainder, and `U i` is the largest dense open gerbe in the
reduced closed substack on that remainder. -/
def IsMaximalDense {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {I : Type (u + 1)} [LinearOrder I] [WellFoundedLT I]
    (U : I → LocallyClosedSubstack X) : Prop :=
  (∀ i, IsReduced (U i).Y) ∧ (∀ i, IsGerbe (U i).Y) ∧
    (∀ i, (U i).pointsSet.Nonempty) ∧
    (⋃ i, (U i).pointsSet) = Set.univ ∧
    (∀ i, IsClosed (remainder U i)) ∧
    (∀ i, (U i).pointsSet ⊆ remainder U i) ∧
    (∀ i, ∃ O : Set (Points X), IsOpen O ∧
      O ∩ remainder U i = (U i).pointsSet) ∧
    (∀ i, remainder U i ⊆ closure (U i).pointsSet) ∧
    (∀ i, ∃ (Z : ClosedSubstack X) (W : OpenSubstack Z.Y),
      Z.pointsSet = remainder U i ∧
        IsReduced Z.Y ∧ IsGerbe W.Y ∧ Dense W.pointsSet ∧
        (∀ W' : OpenSubstack Z.Y, IsGerbe W'.Y → W'.pointsSet ⊆ W.pointsSet) ∧
        (U i).objectProperty =
          LocallyClosedSubstack.imageObjects (W.ι ≫ Z.ι) ∧
        (U i).pointsSet = Set.range (Points.map (W.ι ≫ Z.ι)))

/-- `IsMaximalDense U` unpacks as the type-(a) covering, remainder, density,
and maximality conditions on the family `U`. -/
theorem IsMaximalDense_iff {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] {I : Type (u + 1)} [LinearOrder I] [WellFoundedLT I]
    (U : I → LocallyClosedSubstack X) :
    IsMaximalDense U ↔
      (∀ i, IsReduced (U i).Y) ∧ (∀ i, IsGerbe (U i).Y) ∧
        (∀ i, (U i).pointsSet.Nonempty) ∧
        (⋃ i, (U i).pointsSet) = Set.univ ∧
        (∀ i, IsClosed (remainder U i)) ∧
        (∀ i, (U i).pointsSet ⊆ remainder U i) ∧
        (∀ i, ∃ O : Set (Points X), IsOpen O ∧
          O ∩ remainder U i = (U i).pointsSet) ∧
        (∀ i, remainder U i ⊆ closure (U i).pointsSet) ∧
        (∀ i, ∃ (Z : ClosedSubstack X) (W : OpenSubstack Z.Y),
          Z.pointsSet = remainder U i ∧
            IsReduced Z.Y ∧ IsGerbe W.Y ∧ Dense W.pointsSet ∧
            (∀ W' : OpenSubstack Z.Y, IsGerbe W'.Y →
              W'.pointsSet ⊆ W.pointsSet) ∧
            (U i).objectProperty =
              LocallyClosedSubstack.imageObjects (W.ι ≫ Z.ι) ∧
            (U i).pointsSet = Set.range (Points.map (W.ι ≫ Z.ι))) :=
  sorry

/-- Remark 101.29.4: the open guess that every well-ordered index `I` of a
canonical maximal dense type-(a) gerbe stratification of an algebraic stack
`X` with quasi-compact inertia is countable. The source does not assert this. -/
@[stacks 06RG]
def countableIndex {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] [QuasiCompact (forget.{u + 1, u, u, u + 1} X)] : Prop :=
  ∀ {I : Type (u + 1)} [LinearOrder I] [WellFoundedLT I]
    (U : I → LocallyClosedSubstack X), IsMaximalDense U → Countable I

/-- The open guess `countableIndex X` is the statement that every maximal dense
type-(a) index of `X` is countable. -/
theorem countableIndex_iff {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] [QuasiCompact (forget.{u + 1, u, u, u + 1} X)] :
    countableIndex X ↔
      ∀ {I : Type (u + 1)} [LinearOrder I] [WellFoundedLT I]
        (U : I → LocallyClosedSubstack X), IsMaximalDense U → Countable I :=
  sorry

/-- The open guess `countableIndex X` is equivalent to the source wording that
every maximal dense type-(a) index `I` satisfies
`Cardinal.mk I ≤ Cardinal.aleph0`. -/
theorem countableIndex_iff_mk_le_aleph0 {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] [QuasiCompact (forget.{u + 1, u, u, u + 1} X)] :
    countableIndex X ↔
      ∀ {I : Type (u + 1)} [LinearOrder I] [WellFoundedLT I]
        (U : I → LocallyClosedSubstack X),
        IsMaximalDense U → Cardinal.mk I ≤ Cardinal.aleph0 :=
  sorry

end AlgebraicGeometry.AlgebraicStack.GerbeStratification
