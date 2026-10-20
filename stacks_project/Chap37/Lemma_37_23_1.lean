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
open scoped AlgebraicGeometry nonZeroDivisors

universe u

/- Lemma 37.23.1: a fibre-regular germ in the maximal ideal extends on an affine
neighbourhood to a principal relative effective Cartier divisor that is flat and
locally of finite presentation over the base. -/
@[stacks 056Y]
#check (AlgebraicGeometry.Scheme.Hom.exists_affineOpen_relativeEffectiveCartierDivisor :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f]
    (x : X) (h : X.presheaf.stalk x)
    (hmax : h ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x))
    (hflat : f.flatAt x)
    (hreg : (AlgebraicGeometry.Scheme.Hom.sourceStalkToFiberStalk f x).hom h ∈
      nonZeroDivisors (AlgebraicGeometry.Scheme.Hom.fiberStalkAt f x)),
    ∃ U : X.affineOpens,
      ∃ hxU : x ∈ (U : X.Opens),
        ∃ hU : Γ(X, (U : X.Opens)),
          X.presheaf.germ (U : X.Opens) x hxU hU = h ∧
            let D : (U : X.Opens).toScheme.IdealSheafData :=
              Scheme.IdealSheafData.ofIdealTop
                (Ideal.span ({(U : X.Opens).topIso.inv hU} : Set (Γ((U : X.Opens), ⊤))))
            (⟨x, hxU⟩ ∈ D.support ∧
              IsRelativeEffectiveCartierDivisor ((U : X.Opens).ι ≫ f) D ∧
                LocallyOfFinitePresentation
                  (D.subschemeι ≫ ((U : X.Opens).ι ≫ f))))
