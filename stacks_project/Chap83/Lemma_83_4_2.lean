/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap83.Definition_83_4_1_Quotient
import StacksCheckRecall

/-!
# Uniqueness of categorical quotients
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace.PreRelation

/- Lemma 83.4.2 (1): if a categorical quotient of a pre-relation in algebraic spaces over
`B` exists, equivalently a coequalizer of `P.t` and `P.s` in `Over B`, then it is unique up
to unique isomorphism. -/
@[stacks 048K]
#check
  (AlgebraicGeometry.AlgebraicSpace.PreRelation.IsCategoricalQuotient.existsUniqueIso :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {U X Y : Over B}
      (P : PreRelation U) {φ : U ⟶ X} {ψ : U ⟶ Y},
      P.IsCategoricalQuotient φ → P.IsCategoricalQuotient ψ →
        ∃! e : X ≅ Y, φ ≫ e.hom = ψ)

/- Lemma 83.4.2 (2): if a categorical quotient of a pre-relation in a full subcategory of
algebraic spaces over `B` exists, then it is unique up to unique isomorphism. -/
@[stacks 048K]
#check
  (AlgebraicGeometry.AlgebraicSpace.PreRelation.IsCategoricalQuotientIn.existsUniqueIso :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {U X Y : Over B}
      (P : PreRelation U) (C : ObjectProperty (Over B)) {φ : U ⟶ X} {ψ : U ⟶ Y},
      P.IsCategoricalQuotientIn C φ → P.IsCategoricalQuotientIn C ψ →
        ∃! e : X ≅ Y, φ ≫ e.hom = ψ)

end AlgebraicGeometry.AlgebraicSpace.PreRelation
