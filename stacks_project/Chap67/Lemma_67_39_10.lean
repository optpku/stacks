module

public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap67.Lemma_67_38_8_Unramified

/-!
# Étale morphisms of algebraic spaces are unramified
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 67.39.10: An étale morphism of algebraic spaces is unramified. -/
@[stacks 06CR]
instance unramified_of_etale {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Etale f] : Unramified f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
