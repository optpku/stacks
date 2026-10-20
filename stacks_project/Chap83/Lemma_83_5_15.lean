/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PreRelation.SetTheoretic
import StacksCheckRecall

/-!
# Set-theoretic equivalence relations via points

A pre-relation is a set-theoretic equivalence relation if and only if it is
universally injective and the image of its defining map on `|R|` contains the
images of the diagonal, flip, and transitivity pairings, equivalently if the
induced map on `U(k)` is injective with equivalence-relation image for
algebraically closed fields `k` over `B` of cardinality larger than `lambda R`,
and, when `j` is decent, locally separated, or quasi-separated, for every such
`k`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits
open scoped Cardinal

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.PreRelation

variable {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}

/- Lemma 83.5.15 (1): a pre-relation `j : R ⟶ U ⨯ U` over `B` is a set-theoretic
equivalence relation if and only if `j` is universally injective and
`Set.range (Points.map j.left)` contains the image of `Points.map j'.left` for
each of `j_diag = diag U`, `j_flip = prod.lift P.s P.t`, and
`j_comp = prod.lift (pullback.fst P.s P.t ≫ P.t) (pullback.snd P.s P.t ≫ P.s)`. -/
@[stacks 049X] #check
  (AlgebraicGeometry.AlgebraicSpace.PreRelation.isSetTheoreticEquivalence_iff_universallyInjective_containsListImages :
    ∀ (P : PreRelation U),
    IsSetTheoreticEquivalence P ↔
      UniversallyInjective P.hom.left ∧
        Set.range (Points.map (Limits.diag U).left) ⊆ Set.range (Points.map P.hom.left) ∧
        Set.range (Points.map (prod.lift P.s P.t).left) ⊆
          Set.range (Points.map P.hom.left) ∧
        Set.range (Points.map (prod.lift (pullback.fst P.s P.t ≫ P.t)
            (pullback.snd P.s P.t ≫ P.s)).left) ⊆
          Set.range (Points.map P.hom.left))

/- Lemma 83.5.15 (2): a pre-relation `j : R ⟶ U ⨯ U` over `B` is a set-theoretic
equivalence relation if and only if for every algebraically closed field `k`
over `B` with `lambda P.left.left < #k`, the map `P.pointMap (Over.mk τ)` is
injective and `P.pointRel (Over.mk τ)` is an equivalence relation on `U(k)`. -/
@[stacks 049X] #check
  (AlgebraicGeometry.AlgebraicSpace.PreRelation.isSetTheoreticEquivalence_iff_injectiveEquivOnLargeFieldPoints :
    ∀ (P : PreRelation U),
    IsSetTheoreticEquivalence P ↔
      ∀ {k : Type u} [Field k] [IsAlgClosed k] {σ : Spec (.of k) ⟶ S}
        (τ : ofOver (Over.mk σ) ⟶ B),
        lambda P.left.left < #k →
          Function.Injective (P.pointMap (Over.mk τ)) ∧
            Equivalence (P.pointRel (Over.mk τ)))

/- Lemma 83.5.15 (3): if `j` is decent, locally separated, or quasi-separated,
then a pre-relation `j : R ⟶ U ⨯ U` over `B` is a set-theoretic equivalence
relation if and only if for every algebraically closed field `k` over `B` the
map `P.pointMap (Over.mk τ)` is injective and `P.pointRel (Over.mk τ)` is an
equivalence relation on `U(k)`. -/
@[stacks 049X] #check
  (AlgebraicGeometry.AlgebraicSpace.PreRelation.isSetTheoreticEquivalence_iff_injectiveEquivOnFieldPoints :
    ∀ (P : PreRelation U)
    (h_decent_or_separated :
      Decent P.hom.left ∨ LocallySeparated P.hom.left ∨ QuasiSeparated P.hom.left),
    IsSetTheoreticEquivalence P ↔
      ∀ {k : Type u} [Field k] [IsAlgClosed k] {σ : Spec (.of k) ⟶ S}
        (τ : ofOver (Over.mk σ) ⟶ B),
        Function.Injective (P.pointMap (Over.mk τ)) ∧
          Equivalence (P.pointRel (Over.mk τ)))

end AlgebraicGeometry.AlgebraicSpace.PreRelation
