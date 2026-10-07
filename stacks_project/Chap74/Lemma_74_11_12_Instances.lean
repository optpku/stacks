module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.MorphismProperty.Local
public import stacks_project.Chap67.Lemma_67_28_8_FinitePresentation
public import stacks_project.Chap74.Lemma_74_11_6_Precoverage

/-!
# Finite presentation is fpqc local on the target

Finite presentation for morphisms of algebraic spaces is local on the target
for the fpqc precoverage.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace.FinitePresentation

/-- Finite presentation of morphisms of algebraic spaces is local on the target
for the fpqc precoverage. -/
instance isLocalAtTargetFpqc {S : Scheme.{u}} :
    MorphismProperty.IsLocalAtTarget
      (@FinitePresentation S : MorphismProperty (AlgebraicSpace S))
      (fpqcPrecoverage S) :=
  sorry

/-- A morphism of algebraic spaces is of finite presentation if and only if
every base change along a member of an fpqc covering of the target is of finite
presentation. -/
theorem iff_forall_pullbackSnd_fpqc {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) {R : Presieve Y} (hR : R ∈ (fpqcPrecoverage S).coverings Y) :
    FinitePresentation f ↔
      ∀ {U : AlgebraicSpace S} (g : U ⟶ Y) [HasPullback f g],
        R g → FinitePresentation (pullback.snd f g) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.FinitePresentation
