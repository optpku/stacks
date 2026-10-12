/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.MorphismProperty.Local
public import stacks_project.Chap74.Lemma_74_11_6_Precoverage
public import stacks_project.Chap76.Lemma_76_9_2_Thickening
public import stacks_project.Chap76.Lemma_76_18_1_Thickening

/-!
# Thickenings are fpqc local on the target

Thickenings and first-order thickenings of algebraic spaces over a scheme `S`
satisfy `IsLocalAtTarget` for the fpqc precoverage.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsThickening

/-- Thickenings of algebraic spaces are local on the target for the fpqc
precoverage. -/
instance isLocalAtTargetFpqc {S : Scheme.{u}} :
    MorphismProperty.IsLocalAtTarget
      (@IsThickening S : MorphismProperty (AlgebraicSpace S))
      (fpqcPrecoverage S) :=
  sorry

/-- A morphism of algebraic spaces is a thickening if and only if every base
change along a member of an fpqc covering of the target is a thickening. -/
theorem iff_forall_pullbackSnd_fpqc {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) {R : Presieve Y} (hR : R ∈ (fpqcPrecoverage S).coverings Y) :
    IsThickening f ↔
      ∀ {U : AlgebraicSpace S} (g : U ⟶ Y) [HasPullback f g],
        R g → IsThickening (pullback.snd f g) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.IsThickening

namespace AlgebraicGeometry.AlgebraicSpace.IsFirstOrderThickening

/-- First-order thickenings of algebraic spaces are local on the target for the
fpqc precoverage. -/
instance isLocalAtTargetFpqc {S : Scheme.{u}} :
    MorphismProperty.IsLocalAtTarget
      (@IsFirstOrderThickening S : MorphismProperty (AlgebraicSpace S))
      (fpqcPrecoverage S) :=
  sorry

/-- A morphism of algebraic spaces is a first-order thickening if and only if
every base change along a member of an fpqc covering of the target is a
first-order thickening. -/
theorem iff_forall_pullbackSnd_fpqc {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) {R : Presieve Y} (hR : R ∈ (fpqcPrecoverage S).coverings Y) :
    IsFirstOrderThickening f ↔
      ∀ {U : AlgebraicSpace S} (g : U ⟶ Y) [HasPullback f g],
        R g → IsFirstOrderThickening (pullback.snd f g) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.IsFirstOrderThickening
