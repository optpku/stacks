module

public import Mathlib.CategoryTheory.MorphismProperty.Local
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FiniteLocallyFree.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Sites.FpqcPrecoverage

/-!
# Fpqc locality of finite locally free morphisms

Finite locally free morphisms of algebraic spaces are local on the target for
the fpqc precoverage.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace.FiniteLocallyFree

/-- Finite locally free morphisms of algebraic spaces are local on the target
for the fpqc precoverage. -/
instance isLocalAtTargetFpqc {S : Scheme.{u}} :
    MorphismProperty.IsLocalAtTarget
      (@FiniteLocallyFree S : MorphismProperty (AlgebraicSpace S))
      (fpqcPrecoverage S) :=
  sorry

/-- A morphism of algebraic spaces is finite locally free if and only if every
base change along a member of an fpqc covering of the target is finite locally
free. -/
theorem iff_forall_pullbackSnd_fpqc {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) {R : Presieve Y} (hR : R ∈ (fpqcPrecoverage S).coverings Y) :
    FiniteLocallyFree f ↔
      ∀ {U : AlgebraicSpace S} (g : U ⟶ Y) [HasPullback f g],
        R g → FiniteLocallyFree (pullback.snd f g) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.FiniteLocallyFree
