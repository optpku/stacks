module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.MorphismProperty.Local
public import stacks_project.Chap74.Lemma_74_11_6_Precoverage

/-!
# Isomorphisms are fpqc local on the target

Isomorphisms of algebraic spaces over a scheme `S` satisfy `IsLocalAtTarget`
for the fpqc precoverage.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Isomorphisms

/-- Isomorphisms of algebraic spaces are local on the target for the fpqc
precoverage. -/
instance isLocalAtTargetFpqc {S : Scheme.{u}} :
    MorphismProperty.IsLocalAtTarget
      (MorphismProperty.isomorphisms (AlgebraicSpace S))
      (fpqcPrecoverage S) :=
  sorry

/-- A morphism of algebraic spaces is an isomorphism if and only if every base
change along a member of an fpqc covering of the target is an isomorphism. -/
theorem iff_forall_pullbackSnd_fpqc {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) {R : Presieve Y} (hR : R ∈ (fpqcPrecoverage S).coverings Y) :
    IsIso f ↔
      ∀ {U : AlgebraicSpace S} (g : U ⟶ Y) [HasPullback f g],
        R g → IsIso (pullback.snd f g) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Isomorphisms
