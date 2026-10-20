/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.Relative.Slicing

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/- Lemma 37.23.3: if `f : X ⟶ S` is locally of finite presentation and flat at
`x`, and the fibre stalk at `x` has depth at least one, then an affine
neighbourhood of `x` contains a relative effective Cartier divisor through `x`
whose morphism to `S` is of finite presentation. -/
@[stacks 056Z] #check
  (AlgebraicGeometry.Scheme.Hom.exists_relativeEffectiveCartierDivisor_of_one_le_depth :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f]
      (x : X) (hflat : f.flatAt x),
      (1 : ℕ∞) ≤ moduleDepth (fiberStalkAt f x) (fiberStalkAt f x) →
        ∃ U : X.affineOpens,
          ∃ hxU : x ∈ (U : X.Opens),
            ∃ D : (U : X.Opens).toScheme.IdealSheafData,
              ⟨x, hxU⟩ ∈ D.support ∧
                IsRelativeEffectiveCartierDivisor ((U : X.Opens).ι ≫ f) D ∧
                  Scheme.Hom.FinitePresentation
                    (D.subschemeι ≫ ((U : X.Opens).ι ≫ f)))

end AlgebraicGeometry.Scheme.Hom
