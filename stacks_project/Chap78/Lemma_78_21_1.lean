/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.Functoriality
import StacksCheckRecall

open CategoryTheory

universe u

/- Lemma 78.21.1: Let `S` be a scheme. Let `B` be an algebraic space over `S`. Let
`f : Hom G H` be a morphism of groupoids in algebraic spaces over `B`. Then `f`
induces a canonical 1-morphism `[f] : [U/R] ⟶ [U'/R']` of quotient stacks over
`(Sch/S)_fppf`. -/
@[stacks 046Q] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.Hom.quotientStackMap :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {B : AlgebraicGeometry.AlgebraicSpace S}
      {G H : AlgebraicGeometry.GroupoidAlgebraicSpace B},
      AlgebraicGeometry.GroupoidAlgebraicSpace.Hom G H →
        CategoryTheory.CartesianBasedFunctor
          (AlgebraicGeometry.GroupoidAlgebraicSpace.fppfQuotientStack G).p
          (AlgebraicGeometry.GroupoidAlgebraicSpace.fppfQuotientStack H).p)

#check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.Hom.quotientStackMap_comp :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {B : AlgebraicGeometry.AlgebraicSpace S}
      {G H : AlgebraicGeometry.GroupoidAlgebraicSpace B}
      (f : AlgebraicGeometry.GroupoidAlgebraicSpace.Hom G H),
      (CategoryTheory.CartesianBasedFunctor.precomp
          (AlgebraicGeometry.GroupoidAlgebraicSpace.fppfQuotientStack H).p
          (AlgebraicGeometry.GroupoidAlgebraicSpace.fppfQuotientStackPresentation G).comparison).obj
        (AlgebraicGeometry.GroupoidAlgebraicSpace.Hom.quotientStackMap f) ≅
          AlgebraicGeometry.GroupoidAlgebraicSpace.Hom.prestackToQuotient f)
