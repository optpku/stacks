/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap67.Lemma_67_30_5_Flat

/-!
# Étale morphisms of algebraic spaces are flat
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 67.39.7: An étale morphism of algebraic spaces is flat. -/
@[stacks 0467]
instance flat_of_etale {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Etale f] : Flat f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
