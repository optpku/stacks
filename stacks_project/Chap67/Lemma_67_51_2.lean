module

public import stacks_project.Chap65.Lemma_65_12_4_Immersion
public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap67.Lemma_67_19_5_UniversallyInjective

/-!
# Étale universally injective morphisms of algebraic spaces are open immersions
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 67.51.2: An étale and universally injective morphism of algebraic spaces is an
open immersion. -/
@[stacks 05W5]
instance IsOpenImmersion.of_etale_of_universallyInjective {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Etale f] [UniversallyInjective f] :
    IsOpenImmersion f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
