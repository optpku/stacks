module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.Relative
public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.ClosedImmersion
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening.Affine
public import ReasLib.AlgebraicGeometry.Morphisms.Thickening

/-!
# Relative ampleness and thickenings

This file records invariance of relative ampleness for invertible scheme modules under
morphisms of thickenings.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Thickening.Hom

/-- An invertible module on the ambient source of a morphism of thickenings is relatively
ample exactly when its restriction to the closed source is relatively ample. -/
theorem relativelyAmple_iff {T U : Thickening.{u}} (g : T ⟶ U) (L' : T.right.Modules)
    [Scheme.Modules.Invertible L'] :
    RelativelyAmple g.right L' ↔
      RelativelyAmple g.left ((Scheme.Modules.pullback T.hom).obj L') := sorry

end AlgebraicGeometry.Thickening.Hom
