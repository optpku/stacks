/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.MorphismProperty.Local
public import stacks_project.Chap67.Lemma_67_53_4_UniversalHomeomorphism
public import stacks_project.Chap74.Lemma_74_11_6_Precoverage

/-!
# Universal homeomorphisms are fpqc local on the target

Universal homeomorphisms of algebraic spaces over a scheme `S` satisfy
`IsLocalAtTarget` for the fpqc precoverage.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace.UniversalHomeomorphism

/-- Universal homeomorphisms of morphisms of algebraic spaces are local on the
target for the fpqc precoverage. -/
instance isLocalAtTargetFpqc {S : Scheme.{u}} :
    MorphismProperty.IsLocalAtTarget
      (@UniversalHomeomorphism S : MorphismProperty (AlgebraicSpace S))
      (fpqcPrecoverage S) :=
  sorry

/-- A morphism of algebraic spaces is a universal homeomorphism if and only if
every base change along a member of an fpqc covering of the target is a
universal homeomorphism. -/
theorem iff_forall_pullbackSnd_fpqc {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) {R : Presieve Y} (hR : R ∈ (fpqcPrecoverage S).coverings Y) :
    UniversalHomeomorphism f ↔
      ∀ {U : AlgebraicSpace S} (g : U ⟶ Y) [HasPullback f g],
        R g → UniversalHomeomorphism (pullback.snd f g) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.UniversalHomeomorphism
