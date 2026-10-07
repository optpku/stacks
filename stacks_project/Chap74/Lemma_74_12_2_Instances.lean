module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.MorphismProperty.Local
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap73.Lemma_73_7_3_Precoverage

/-!
# Locally separated morphisms are fppf local on the target

Locally separated morphisms of algebraic spaces over a scheme `S` satisfy
`IsLocalAtTarget` for the fppf precoverage.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace.LocallySeparated

/-- Locally separated morphisms of algebraic spaces are local on the target for
the fppf precoverage. -/
instance isLocalAtTargetFppf {S : Scheme.{u}} :
    MorphismProperty.IsLocalAtTarget
      (@LocallySeparated S : MorphismProperty (AlgebraicSpace S))
      (fppfPrecoverage S) :=
  sorry

/-- A morphism of algebraic spaces is locally separated if and only if every
base change along a member of an fppf covering of the target is locally
separated. -/
theorem iff_forall_pullbackSnd_fppf {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) {R : Presieve Y} (hR : R ∈ (fppfPrecoverage S).coverings Y) :
    LocallySeparated f ↔
      ∀ {U : AlgebraicSpace S} (g : U ⟶ Y) [HasPullback f g],
        R g → LocallySeparated (pullback.snd f g) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.LocallySeparated
