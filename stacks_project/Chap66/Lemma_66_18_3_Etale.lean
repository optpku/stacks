/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Lemma_66_16_4_Etale

/-!
# Étale morphisms from schemes into algebraic spaces

A morphism from a scheme to an algebraic space is étale when the corresponding
transformation of functors of points is representable and étale in the sense of
Spaces, Definition 65.5.1. This is the scheme-source ingredient of the étale
morphism class of algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism from a scheme `U` over `S` to an algebraic space `X` is étale when the
corresponding transformation of functors of points is representable and étale as a morphism of
schemes. -/
def isEtaleFromScheme {S : Scheme.{u}} {U : Over S} {X : AlgebraicSpace S}
    (f : ofOver U ⟶ X) : Prop :=
  (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf f

/-- `isEtaleFromScheme f` is the relative étale presheaf property of `f`. -/
theorem isEtaleFromScheme_def {S : Scheme.{u}} {U : Over S} {X : AlgebraicSpace S}
    (f : ofOver U ⟶ X) :
    isEtaleFromScheme f ↔
      (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf f :=
  Iff.rfl

/-- A morphism from a scheme, viewed as an algebraic space, is étale if and only if it is étale
as a morphism from a scheme to an algebraic space. -/
theorem isEtale_iff_isEtaleFromScheme {S : Scheme.{u}} {U : Over S} {X : AlgebraicSpace S}
    (f : ofOver U ⟶ X) : Etale f ↔ isEtaleFromScheme f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
