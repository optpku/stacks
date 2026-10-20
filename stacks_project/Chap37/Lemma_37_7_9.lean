/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening.UniversalFirstOrder.Differentials
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped RelativeDerivation
open AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.Thickening.IsUniversalFirstOrder

variable {X S : Scheme.{u}} (T : Thickening.Over X) (f : X ⟶ S)
  [FormallyUnramified T.left.hom] [IsUniversalFirstOrder T]

/- Lemma 37.7.9: for a universal first-order thickening of a formally unramified
morphism, pulling the canonical relative-differentials comparison back to the closed part
is an isomorphism. -/
@[stacks 04FB]
#check (AlgebraicGeometry.Thickening.IsUniversalFirstOrder.pullbackDifferentialsComparison_isIso
  T f : IsIso
    ((pullbackCongr T.hom.w).inv.app Ω[f.toShHom] ≫
      (pullbackComp T.hom.left T.right.hom).inv.app Ω[f.toShHom] ≫
        (pullback T.hom.left).map
          (AlgebraicGeometry.Scheme.Hom.Conormal.Differentials.comparison
            T.right.hom f)))

end AlgebraicGeometry.Thickening.IsUniversalFirstOrder
