/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.MorphismProperty.Local
public import stacks_project.Chap65.Lemma_65_12_4_Immersion
public import stacks_project.Chap73.Lemma_73_7_3_Precoverage

/-!
# Immersions are fppf local on the target

Immersions of algebraic spaces over a scheme `S` satisfy `IsLocalAtTarget`
for the fppf precoverage.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsImmersion

/-- Immersions of algebraic spaces are local on the target for the fppf
precoverage. -/
instance isLocalAtTargetFppf {S : Scheme.{u}} :
    MorphismProperty.IsLocalAtTarget
      (@IsImmersion S : MorphismProperty (AlgebraicSpace S))
      (fppfPrecoverage S) :=
  sorry

/-- A morphism of algebraic spaces is an immersion if and only if every base
change along a member of an fppf covering of the target is an immersion. -/
theorem iff_forall_pullbackSnd_fppf {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) {R : Presieve Y} (hR : R ∈ (fppfPrecoverage S).coverings Y) :
    IsImmersion f ↔
      ∀ {U : AlgebraicSpace S} (g : U ⟶ Y) [HasPullback f g],
        R g → IsImmersion (pullback.snd f g) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.IsImmersion
