/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap78.Lemma_78_21_1_QuotientMap
import StacksCheckRecall

universe u

/- Lemma 78.21.1: Let `S` be a scheme. Let `B` be an algebraic space over `S`. Let
`f : Hom G H` be a morphism of groupoids in algebraic spaces over `B`. Then `f`
induces a canonical 1-morphism `[f] : [U/R] ⟶ [U'/R']` of quotient stacks over
`(Sch/S)_fppf`. -/
@[stacks 046Q] #check
  (@AlgebraicGeometry.GroupoidAlgebraicSpace.Hom.quotientStackMap :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {B : AlgebraicGeometry.AlgebraicSpace S}
      {G H : AlgebraicGeometry.GroupoidAlgebraicSpace B},
      AlgebraicGeometry.GroupoidAlgebraicSpace.Hom G H →
        CategoryTheory.CartesianBasedFunctor
          (AlgebraicGeometry.GroupoidAlgebraicSpace.fppfQuotientStack G).p
          (AlgebraicGeometry.GroupoidAlgebraicSpace.fppfQuotientStack H).p)

#check AlgebraicGeometry.GroupoidAlgebraicSpace.Hom.quotientStackMap_comp
