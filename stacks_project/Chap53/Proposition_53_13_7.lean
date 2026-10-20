/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Curve.Frobenius

@[expose] public section

open AlgebraicGeometry CategoryTheory
open Scheme.Hom
open Scheme.Hom.IsNonconstant

universe u

namespace AlgebraicGeometry.Curve

/- Proposition 53.13.7: a nonconstant morphism of proper smooth curves in
characteristic `p > 0` factors through a canonical iterated Frobenius twist;
the residual morphism is nonconstant and induces a separable function-field
extension. -/
@[stacks 0CD2]
#check
  (AlgebraicGeometry.Curve.existsIteratedRelativeFrobeniusSeparableFactorization :
    ∀ {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
      (X Y : SchemeOverField k) [Curve X] [Curve Y]
      [IsProper X.hom] [IsProper Y.hom] [Smooth X.hom] [Smooth Y.hom]
      (f : X ⟶ Y) (hf : f.left.IsNonconstant),
      ∃ (n : ℕ) (g : @Scheme.pPowerTwist p inferInstance _ _ X.hom inferInstance n ⟶ Y),
        ∃ (h_curve : Curve (@Scheme.pPowerTwist p inferInstance _ _ X.hom inferInstance n)),
        ∃ (h_proper : IsProper (@Scheme.pPowerTwist p inferInstance _ _ X.hom inferInstance n).hom),
        ∃ (h_smooth : Smooth (@Scheme.pPowerTwist p inferInstance _ _ X.hom inferInstance n).hom),
          ∃ (h_nonconstant : g.left.IsNonconstant),
            @Scheme.iteratedRelativeFrobenius p inferInstance _ _ X.hom inferInstance n ≫ g = f ∧
              @Algebra.IsSeparable Y.left.functionField
                (@Scheme.pPowerTwist p inferInstance _ _ X.hom inferInstance n).left.functionField
                inferInstance inferInstance
                (@Scheme.Hom.functionFieldAlgebra _ _ g.left
                  h_curve.toVariety.toIsIntegral inferInstance
                  (@Scheme.Hom.map_genericPoint_eq_of_isDominant _ _ g.left
                    h_curve.toVariety.toIsIntegral inferInstance
                    (@isDominant_of_curves k _ _ _ h_curve inferInstance
                      g h_nonconstant))))
end AlgebraicGeometry.Curve
