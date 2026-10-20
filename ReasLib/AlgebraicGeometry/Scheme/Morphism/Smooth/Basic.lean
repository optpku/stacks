module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Pointwise and affine standard smooth scheme morphisms

This file relates the global smoothness property to smoothness at each point and
defines standard smoothness for morphisms between affine schemes.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry
namespace Scheme.Hom

variable {X S : Scheme.{u}}

/-- A scheme morphism is smooth at `x` when there are compatible affine neighborhoods of `x`
and its image for which the induced map on coordinate rings is smooth. -/
def SmoothAt (f : X ⟶ S) (x : X) : Prop :=
  ∃ V : S.affineOpens, ∃ U : X.affineOpens,
    x ∈ (U : X.Opens) ∧ ∃ e : (U : X.Opens) ≤ f ⁻¹ᵁ (V : S.Opens),
      (f.appLE (V : S.Opens) (U : X.Opens) e).hom.Smooth

/-- A scheme morphism is smooth at a point exactly when compatible affine neighborhoods exist
for which the induced map on coordinate rings is smooth. -/
theorem smoothAt_iff (f : X ⟶ S) (x : X) :
    f.SmoothAt x ↔
      ∃ V : S.affineOpens, ∃ U : X.affineOpens,
        x ∈ (U : X.Opens) ∧ ∃ e : (U : X.Opens) ≤ f ⁻¹ᵁ (V : S.Opens),
          (f.appLE (V : S.Opens) (U : X.Opens) e).hom.Smooth := sorry

/-- A scheme morphism is smooth exactly when it is smooth at every point of its source. -/
theorem smooth_iff_forall_smoothAt (f : X ⟶ S) :
    Smooth f ↔ ∀ x : X, f.SmoothAt x := sorry

end Scheme.Hom

variable {X S : Scheme.{u}}

/-- A morphism between affine schemes is standard smooth when its global-sections ring
homomorphism is standard smooth. -/
abbrev StandardSmooth (f : X ⟶ S) [IsAffine X] [IsAffine S] : Prop :=
  RingHom.IsStandardSmooth (CommRingCat.Hom.hom (Scheme.Hom.appTop f))

/-- Standard smoothness of an affine scheme morphism is exactly standard smoothness of its
global-sections ring homomorphism. -/
theorem standardSmooth_iff (f : X ⟶ S) [IsAffine X] [IsAffine S] :
    StandardSmooth f ↔
      RingHom.IsStandardSmooth (CommRingCat.Hom.hom (Scheme.Hom.appTop f)) := sorry

end AlgebraicGeometry
