/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.Slicing.Separable

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open TopologicalSpace
open scoped AlgebraicGeometry

universe u

/- Lemma 37.38.4: a smooth point with separable residue-field extension that
is not generic in its fibre lies on an effective Cartier divisor in an affine
neighbourhood whose morphism to the base is smooth. -/
@[stacks 057F] #check
  (AlgebraicGeometry.Scheme.Hom.SmoothAt.exists_affineOpen_smoothEffectiveCartierDivisor_of_separable :
    ∀ {X S : Scheme.{u}} {f : X ⟶ S} {x : X},
    f.SmoothAt x →
    ∀ [Algebra.IsSeparableOver (S.residueField (f x)) (X.residueField x)],
    f.asFiber x ∉ genericPoints (f.fiber (f x)) →
    ∃ U : X.affineOpens,
      ∃ hxU : x ∈ (U : X.Opens),
        ∃ D : (U : X.Opens).toScheme.IdealSheafData,
          ⟨x, hxU⟩ ∈ D.support ∧
            IsRelativeEffectiveCartierDivisor ((U : X.Opens).ι ≫ f) D ∧
              Smooth (D.subschemeι ≫ ((U : X.Opens).ι ≫ f)))
