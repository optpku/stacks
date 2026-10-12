/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Order.Hom.Basic
public import Mathlib.Order.RelClasses
public import stacks_project.Chap100.Definition_100_6_1_QuasiCompact
public import stacks_project.Chap100.Lemma_100_9_12_Opens
public import stacks_project.Chap100.Lemma_100_10_1_Points
public import stacks_project.Chap100.Lemma_100_11_2_Reduced
public import stacks_project.Chap101.Definition_101_7_2_QuasiCompact
public import stacks_project.Chap101.Definition_101_28_1_Gerbe
public import stacks_project.Chap101.Lemma_101_5_1
public import stacks_project.Chap101.Lemma_101_29_3_Stratum

/-!
# Stratification of an algebraic stack by gerbes

An algebraic stack with quasi-compact inertia admits a well-ordered covering by
reduced locally closed gerbe substacks, which may be arranged to be dense in
the successive remainders or to be quasi-compact. The maximal dense choice is
canonical up to order isomorphism of the index and equality of
`objectProperty`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids.Inertia (forget)
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.GerbeStratification

/-- Lemma 101.29.3 (1): Let `X` be an algebraic stack such that `I_X ⟶ X` is
quasi-compact. Then there exists a well-ordered index set `I` and for every
`i : I` a reduced locally closed substack `U i ⊂ X` which is a gerbe, covering
`|X|` by `|U i|`, with each remainder `T i = |X| \ ⋃ i' < i, |U i'|` closed
and `|U i|` open in `T i`, arranged so that `|U i|` is dense in `T i`. -/
@[stacks 06RF]
theorem exists_dense {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] [QuasiCompact (forget.{u + 1, u, u, u + 1} X)] :
    ∃ (I : Type (u + 1)) (_ : LinearOrder I) (_ : WellFoundedLT I)
      (U : I → LocallyClosedSubstack X),
      (∀ i, IsReduced (U i).Y) ∧ (∀ i, IsGerbe (U i).Y) ∧
        (∀ i, (U i).pointsSet.Nonempty) ∧
        (⋃ i, (U i).pointsSet) = Set.univ ∧
        (∀ i, IsClosed (remainder U i)) ∧
        (∀ i, (U i).pointsSet ⊆ remainder U i) ∧
        (∀ i, ∃ V : Set (Points X), IsOpen V ∧
          V ∩ remainder U i = (U i).pointsSet) ∧
        (∀ i, remainder U i ⊆ closure (U i).pointsSet) :=
  sorry

/-- Lemma 101.29.3 (2): Let `X` be an algebraic stack such that `I_X ⟶ X` is
quasi-compact. Then there exists a well-ordered index set `I` and for every
`i : I` a reduced locally closed substack `U i ⊂ X` which is a gerbe, covering
`|X|` by `|U i|`, with each remainder `T i = |X| \ ⋃ i' < i, |U i'|` closed
and `|U i|` open in `T i`, arranged so that each `U i` is quasi-compact. -/
@[stacks 06RF]
theorem exists_quasiCompact {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] [QuasiCompact (forget.{u + 1, u, u, u + 1} X)] :
    ∃ (I : Type (u + 1)) (_ : LinearOrder I) (_ : WellFoundedLT I)
      (U : I → LocallyClosedSubstack X),
      (∀ i, IsReduced (U i).Y) ∧ (∀ i, IsGerbe (U i).Y) ∧
        (∀ i, (U i).pointsSet.Nonempty) ∧
        (⋃ i, (U i).pointsSet) = Set.univ ∧
        (∀ i, IsClosed (remainder U i)) ∧
        (∀ i, (U i).pointsSet ⊆ remainder U i) ∧
        (∀ i, ∃ V : Set (Points X), IsOpen V ∧
          V ∩ remainder U i = (U i).pointsSet) ∧
        (∀ i, IsQuasiCompact (U i).Y) :=
  sorry

/-- Lemma 101.29.3 (3): Let `X` be an algebraic stack such that `I_X ⟶ X` is
quasi-compact. In the dense arrangement, if each stratum `U i` is the largest
dense open gerbe of the unique reduced closed substack `Z ⊂ X` with
`|Z| = T i`, then the stratification is canonical: any two such families
agree on `objectProperty` along an order isomorphism of indices. -/
@[stacks 06RF]
theorem unique_maximal_dense {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] [QuasiCompact (forget.{u + 1, u, u, u + 1} X)]
    {I J : Type (u + 1)}
    [LinearOrder I] [WellFoundedLT I] [LinearOrder J] [WellFoundedLT J]
    (U : I → LocallyClosedSubstack X) (V : J → LocallyClosedSubstack X)
    (hU_reduced : ∀ i, IsReduced (U i).Y) (hU_gerbe : ∀ i, IsGerbe (U i).Y)
    (hU_nonempty : ∀ i, (U i).pointsSet.Nonempty)
    (hU_cover : (⋃ i, (U i).pointsSet) = Set.univ)
    (hU_closed : ∀ i, IsClosed (remainder U i))
    (hU_subset : ∀ i, (U i).pointsSet ⊆ remainder U i)
    (hU_open : ∀ i, ∃ O : Set (Points X), IsOpen O ∧
      O ∩ remainder U i = (U i).pointsSet)
    (hU_dense : ∀ i, remainder U i ⊆ closure (U i).pointsSet)
    (hU_max : ∀ i, ∃ (Z : ClosedSubstack X) (W : OpenSubstack Z.Y),
      Z.pointsSet = remainder U i ∧
        IsReduced Z.Y ∧ IsGerbe W.Y ∧ Dense W.pointsSet ∧
        (∀ W' : OpenSubstack Z.Y, IsGerbe W'.Y → W'.pointsSet ⊆ W.pointsSet) ∧
        (U i).objectProperty =
          LocallyClosedSubstack.imageObjects (W.ι ≫ Z.ι) ∧
        (U i).pointsSet = Set.range (Points.map (W.ι ≫ Z.ι)))
    (hV_reduced : ∀ j, IsReduced (V j).Y) (hV_gerbe : ∀ j, IsGerbe (V j).Y)
    (hV_nonempty : ∀ j, (V j).pointsSet.Nonempty)
    (hV_cover : (⋃ j, (V j).pointsSet) = Set.univ)
    (hV_closed : ∀ j, IsClosed (remainder V j))
    (hV_subset : ∀ j, (V j).pointsSet ⊆ remainder V j)
    (hV_open : ∀ j, ∃ O : Set (Points X), IsOpen O ∧
      O ∩ remainder V j = (V j).pointsSet)
    (hV_dense : ∀ j, remainder V j ⊆ closure (V j).pointsSet)
    (hV_max : ∀ j, ∃ (Z : ClosedSubstack X) (W : OpenSubstack Z.Y),
      Z.pointsSet = remainder V j ∧
        IsReduced Z.Y ∧ IsGerbe W.Y ∧ Dense W.pointsSet ∧
        (∀ W' : OpenSubstack Z.Y, IsGerbe W'.Y → W'.pointsSet ⊆ W.pointsSet) ∧
        (V j).objectProperty =
          LocallyClosedSubstack.imageObjects (W.ι ≫ Z.ι) ∧
        (V j).pointsSet = Set.range (Points.map (W.ι ≫ Z.ι))) :
    ∃ e : I ≃o J, ∀ i, (U i).objectProperty = (V (e i)).objectProperty :=
  sorry

end AlgebraicGeometry.AlgebraicStack.GerbeStratification
