module

public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Lemma_67_24_2_Lambda
public import stacks_project.Chap83.Definition_83_5_13_SetTheoretic

/-!
# Set-theoretic pre-equivalence relations via points

A pre-relation is a set-theoretic pre-equivalence relation if and only if the
image of its defining map on `|R|` contains the images of the diagonal, flip,
and transitivity pairings, equivalently if the induced relation on `U(k)` is an
equivalence relation for algebraically closed fields `k` over `B` of cardinality
larger than `lambda R`, and, when `s` and `t` are locally of finite type, for
every such `k`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits
open scoped Cardinal

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.PreRelation

variable {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}

/-- Lemma 83.5.14 (1): a pre-relation `j : R ⟶ U ⨯ U` over `B` is a set-theoretic
pre-equivalence relation if and only if `Set.range (Points.map j.left)` contains
the image of `Points.map j'.left` for each of `j_diag = diag U`,
`j_flip = prod.lift P.s P.t`, and
`j_comp = prod.lift (pullback.fst P.s P.t ≫ P.t) (pullback.snd P.s P.t ≫ P.s)`. -/
@[stacks 0491]
theorem isSetTheoreticPreEquivalence_iff_containsListImages (P : PreRelation U) :
    P.IsSetTheoreticPreEquivalence ↔
      Set.range (Points.map (diag U).left) ⊆ Set.range (Points.map P.hom.left) ∧
        Set.range (Points.map (prod.lift P.s P.t).left) ⊆
          Set.range (Points.map P.hom.left) ∧
        Set.range (Points.map (prod.lift (pullback.fst P.s P.t ≫ P.t)
            (pullback.snd P.s P.t ≫ P.s)).left) ⊆
          Set.range (Points.map P.hom.left) :=
  sorry

/-- Lemma 83.5.14 (2): a pre-relation `j : R ⟶ U ⨯ U` over `B` is a set-theoretic
pre-equivalence relation if and only if for every algebraically closed field `k`
over `B` with `lambda P.left.left < #k`, the relation `P.pointRel (Over.mk τ)` is
an equivalence relation on `U(k)`. -/
@[stacks 0491]
theorem isSetTheoreticPreEquivalence_iff_equivOnLargeFieldPoints (P : PreRelation U) :
    P.IsSetTheoreticPreEquivalence ↔
      ∀ {k : Type u} [Field k] [IsAlgClosed k] {σ : Spec (.of k) ⟶ S}
        (τ : ofOver (Over.mk σ) ⟶ B),
        lambda P.left.left < #k → Equivalence (P.pointRel (Over.mk τ)) :=
  sorry

/-- Lemma 83.5.14 (3): if `s` and `t` are locally of finite type, then a pre-relation
`j : R ⟶ U ⨯ U` over `B` is a set-theoretic pre-equivalence relation if and only if
for every algebraically closed field `k` over `B` the relation
`P.pointRel (Over.mk τ)` is an equivalence relation on `U(k)`. -/
@[stacks 0491]
theorem isSetTheoreticPreEquivalence_iff_equivOnFieldPoints (P : PreRelation U)
    [LocallyOfFiniteType P.s.left] [LocallyOfFiniteType P.t.left] :
    P.IsSetTheoreticPreEquivalence ↔
      ∀ {k : Type u} [Field k] [IsAlgClosed k] {σ : Spec (.of k) ⟶ S}
        (τ : ofOver (Over.mk σ) ⟶ B), Equivalence (P.pointRel (Over.mk τ)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.PreRelation
