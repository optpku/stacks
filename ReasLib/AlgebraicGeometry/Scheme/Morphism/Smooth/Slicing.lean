/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.Relative.Slicing
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.AtPoint
public import Mathlib.Algebra.Category.ModuleCat.Differentials.Basic

/-!
# Slicing smooth morphisms

This file constructs smooth relative effective Cartier divisors by extending a germ whose
relative differential is nonzero at a smooth point.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry nonZeroDivisors TensorProduct

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A germ in the maximal ideal whose relative differential is nonzero at a smooth point
extends on an affine neighbourhood to an equation for an effective Cartier divisor through
the point that is smooth over the base. -/
theorem SmoothAt.exists_affineOpen_smoothEffectiveCartierDivisor
    {X S : Scheme.{u}} {f : X ⟶ S} {x : X}
    (hf : f.SmoothAt x) (h : X.presheaf.stalk x)
    (hmax : h ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x))
    (hdiff : (1 : X.residueField x) ⊗ₜ[X.presheaf.stalk x]
      (CommRingCat.KaehlerDifferential.d h :
        CommRingCat.KaehlerDifferential (f.stalkMap x)) ≠ 0) :
    ∃ U : X.affineOpens,
      ∃ hxU : x ∈ (U : X.Opens),
        ∃ hU : Γ(X, (U : X.Opens)),
          X.presheaf.germ (U : X.Opens) x hxU hU = h ∧
            let D : (U : X.Opens).toScheme.IdealSheafData :=
              Scheme.IdealSheafData.ofIdealTop
                (Ideal.span ({(U : X.Opens).topIso.inv hU} : Set (Γ((U : X.Opens), ⊤))))
            (⟨x, hxU⟩ ∈ D.support ∧
              IsRelativeEffectiveCartierDivisor ((U : X.Opens).ι ≫ f) D ∧
              Smooth (D.subschemeι ≫ ((U : X.Opens).ι ≫ f))) := sorry

/-- If a morphism is smooth at a point and the canonical Kähler-differential base-change
map from the fibre stalk to the residue field has nontrivial kernel, then an affine
neighbourhood contains an effective Cartier divisor through the point that is smooth over
the base. -/
theorem SmoothAt.exists_smoothEffectiveCartierDivisor
    {X S : Scheme.{u}} {f : X ⟶ S} {x : X}
    (hf : f.SmoothAt x)
    (hker : ¬ Function.Injective
      (KaehlerDifferential.mapBaseChange
        (S.residueField (f x)) (fiberStalkAt f x) (X.residueField x))) :
    ∃ U : X.affineOpens,
      ∃ hxU : x ∈ (U : X.Opens),
        ∃ D : (U : X.Opens).toScheme.IdealSheafData,
          ⟨x, hxU⟩ ∈ D.support ∧
            IsEffectiveCartierDivisor D.subschemeι ∧
            Smooth (D.subschemeι ≫ ((U : X.Opens).ι ≫ f)) := sorry

end AlgebraicGeometry.Scheme.Hom
