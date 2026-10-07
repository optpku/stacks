module

public import stacks_project.Chap73.Definition_73_8_1_PhCovering
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap67.Definition_67_5_2_Surjective

/-!
# Singleton proper-surjective ph coverings of algebraic spaces

A surjective proper morphism of algebraic spaces, viewed as a singleton family,
is a ph covering.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A surjective proper morphism of algebraic spaces, regarded as a singleton
family, is a ph covering. -/
instance phCoveringSingletonOfProperSurjective {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : Y ⟶ X) [Proper f] [Surjective f] :
    PhCovering (fun _ : PUnit ↦ Y) (fun _ ↦ f) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
