/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap67.Definition_67_40_1_FiniteType

/-!
# Étale morphisms of algebraic spaces are locally of finite type
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 67.39.9: An étale morphism of algebraic spaces is locally of finite type. -/
@[stacks 06LT]
instance locallyOfFiniteType_of_etale {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Etale f] : LocallyOfFiniteType f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
