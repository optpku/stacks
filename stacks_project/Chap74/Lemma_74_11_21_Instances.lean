/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.MorphismProperty.Local
public import stacks_project.Chap67.Definition_67_8_2_QuasiCompact
public import stacks_project.Chap65.Lemma_65_12_4_Immersion
public import stacks_project.Chap74.Lemma_74_11_6_Precoverage

/-!
# Quasi-compact immersions are fpqc local on the target

Quasi-compact immersions of algebraic spaces over a scheme `S` satisfy
`IsLocalAtTarget` for the fpqc precoverage.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace.QuasiCompactImmersion

/-- Quasi-compact immersions of algebraic spaces are local on the target for the
fpqc precoverage. -/
instance isLocalAtTargetFpqc {S : Scheme.{u}} :
    MorphismProperty.IsLocalAtTarget
      (@QuasiCompact S ⊓ @IsImmersion S : MorphismProperty (AlgebraicSpace S))
      (fpqcPrecoverage S) :=
  sorry

/-- A morphism of algebraic spaces is a quasi-compact immersion if and only if
every base change along a member of an fpqc covering of the target is a
quasi-compact immersion. -/
theorem iff_forall_pullbackSnd_fpqc {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) {R : Presieve Y} (hR : R ∈ (fpqcPrecoverage S).coverings Y) :
    QuasiCompact f ∧ IsImmersion f ↔
      ∀ {U : AlgebraicSpace S} (g : U ⟶ Y) [HasPullback f g],
        R g → QuasiCompact (pullback.snd f g) ∧ IsImmersion (pullback.snd f g) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.QuasiCompactImmersion
