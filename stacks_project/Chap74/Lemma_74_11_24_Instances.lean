module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.MorphismProperty.Local
public import stacks_project.Chap67.Lemma_67_27_3_QuasiFinite
public import stacks_project.Chap74.Lemma_74_11_6_Precoverage

/-!
# Locally quasi-finite and quasi-finite morphisms are fpqc local on the target

Stacks locally quasi-finite morphisms of algebraic spaces — locally of finite
type and locally quasi-finite — and quasi-finite morphisms are local on the
target for the fpqc precoverage.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace.FiniteType

/-- Locally quasi-finite morphisms of algebraic spaces, in the Stacks sense of
locally of finite type and locally quasi-finite, are local on the target for
the fpqc precoverage. -/
instance locallyQuasiFinite_isLocalAtTargetFpqc {S : Scheme.{u}} :
    MorphismProperty.IsLocalAtTarget
      (@LocallyOfFiniteType S ⊓ @LocallyQuasiFinite S :
        MorphismProperty (AlgebraicSpace S))
      (fpqcPrecoverage S) :=
  sorry

/-- A morphism of algebraic spaces is locally quasi-finite in the Stacks sense
if and only if every base change along a member of an fpqc covering of the
target is locally quasi-finite in that sense. -/
theorem locallyQuasiFinite_iff_forall_pullbackSnd_fpqc {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) {R : Presieve Y}
    (hR : R ∈ (fpqcPrecoverage S).coverings Y) :
    LocallyOfFiniteType f ∧ LocallyQuasiFinite f ↔
      ∀ {U : AlgebraicSpace S} (g : U ⟶ Y) [HasPullback f g],
        R g → LocallyOfFiniteType (pullback.snd f g) ∧
          LocallyQuasiFinite (pullback.snd f g) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.FiniteType

namespace AlgebraicGeometry.AlgebraicSpace.QuasiFinite

/-- Quasi-finiteness of morphisms of algebraic spaces is local on the target for
the fpqc precoverage. -/
instance isLocalAtTargetFpqc {S : Scheme.{u}} :
    MorphismProperty.IsLocalAtTarget
      (@QuasiFinite S : MorphismProperty (AlgebraicSpace S))
      (fpqcPrecoverage S) :=
  sorry

/-- A morphism of algebraic spaces is quasi-finite if and only if every base
change along a member of an fpqc covering of the target is quasi-finite. -/
theorem iff_forall_pullbackSnd_fpqc {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) {R : Presieve Y} (hR : R ∈ (fpqcPrecoverage S).coverings Y) :
    QuasiFinite f ↔
      ∀ {U : AlgebraicSpace S} (g : U ⟶ Y) [HasPullback f g],
        R g → QuasiFinite (pullback.snd f g) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.QuasiFinite
