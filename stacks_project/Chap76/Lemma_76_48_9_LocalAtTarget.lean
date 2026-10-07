module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.MorphismProperty.Local
public import stacks_project.Chap74.Lemma_74_11_6_Precoverage
public import stacks_project.Chap76.Definition_76_48_1_LocalCompleteIntersection

/-!
# Local complete intersection morphisms are fpqc local on the target

Local complete intersection morphisms of algebraic spaces over a scheme `S`
satisfy `IsLocalAtTarget` for the fpqc precoverage.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsLocalCompleteIntersection

/-- Local complete intersection morphisms of algebraic spaces are local on the
target for the fpqc precoverage. -/
instance isLocalAtTargetFpqc {S : Scheme.{u}} :
    MorphismProperty.IsLocalAtTarget
      (@IsLocalCompleteIntersection S : MorphismProperty (AlgebraicSpace S))
      (fpqcPrecoverage S) :=
  sorry

/-- A morphism of algebraic spaces is a local complete intersection if and only
if every base change along a member of an fpqc covering of the target is a
local complete intersection. -/
theorem iff_forall_pullbackSnd_fpqc {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) {R : Presieve Y} (hR : R ∈ (fpqcPrecoverage S).coverings Y) :
    IsLocalCompleteIntersection f ↔
      ∀ {U : AlgebraicSpace S} (g : U ⟶ Y) [HasPullback f g],
        R g → IsLocalCompleteIntersection (pullback.snd f g) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.IsLocalCompleteIntersection
