module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening.Restriction
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening.UniversalFirstOrder.BaseChange

/-!
# Restrictions of universal first-order thickenings

Universal first-order thickenings remain universal after restriction to compatible open
subschemes. The corresponding cartesian square also induces an isomorphism on conormal sheaves.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Thickening.IsUniversalFirstOrder

/-- Restriction to compatible opens preserves universal first-order thickenings. -/
instance restrict {X : Scheme.{u}} (T : Thickening.Over X)
    (U : X.Opens) (V : T.left.left.Opens) (hV : V ≤ T.left.hom ⁻¹ᵁ U)
    [IsUniversalFirstOrder T] :
    IsUniversalFirstOrder (Thickening.Over.restrict T U V hV) := sorry

/-- The transported ambient open pulls back to the prescribed closed open, and the resulting
restricted thickening is universal to first order. -/
theorem restrict_spec {X : Scheme.{u}} (T : Thickening.Over X)
    (U : X.Opens) (V : T.left.left.Opens) (hV : V ≤ T.left.hom ⁻¹ᵁ U)
    [FormallyUnramified T.left.hom] [IsUniversalFirstOrder T] :
    T.hom.left ⁻¹ᵁ (IsThickening.opensEquiv T.hom.left V) = V ∧
      IsUniversalFirstOrder (Thickening.Over.restrict T U V hV) := sorry

/-- The canonical conormal comparison for restriction of a universal first-order thickening
to compatible opens is an isomorphism. -/
theorem restrictConormalMap_isIso {X : Scheme.{u}} (T : Thickening.Over X)
    (U : X.Opens) (V : T.left.left.Opens) (hV : V ≤ T.left.hom ⁻¹ᵁ U)
    [FormallyUnramified T.left.hom] [IsUniversalFirstOrder T] :
    IsIso (Scheme.Hom.Conormal.map
      (Thickening.Over.restrictSquare T U V hV).toCommSq) := sorry

end AlgebraicGeometry.Thickening.IsUniversalFirstOrder
