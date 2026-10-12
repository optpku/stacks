/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Differentials.Conormal
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening.UniversalFirstOrder.Restriction

/-!
# Differentials of universal first-order thickenings

The canonical relative-differentials comparison for a universal first-order thickening of a
formally unramified morphism becomes an isomorphism after pullback to the closed subscheme.
-/

@[expose] public section

open CategoryTheory
open scoped RelativeDerivation
open AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.Thickening.IsUniversalFirstOrder

/-- Pulling the canonical relative-differentials comparison for a universal first-order
thickening of a formally unramified morphism back to its closed subscheme is an isomorphism. -/
theorem pullbackDifferentialsComparison_isIso {X S : Scheme.{u}}
    (T : Thickening.Over X) (f : X ⟶ S)
    [FormallyUnramified T.left.hom] [IsUniversalFirstOrder T] :
    IsIso
      ((pullbackCongr T.hom.w).inv.app Ω[f.toShHom] ≫
        (pullbackComp T.hom.left T.right.hom).inv.app Ω[f.toShHom] ≫
          (pullback T.hom.left).map
            (AlgebraicGeometry.Scheme.Hom.Conormal.Differentials.comparison
              T.right.hom f)) := sorry

end AlgebraicGeometry.Thickening.IsUniversalFirstOrder
