/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberIntegral

/-!
# Fibre-integral compatibility bridge

This module re-exports the reusable fibre-integral definition and its pointwise
finite-sum formula under the historical chapter import path.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

#check (AlgebraicGeometry.Scheme.Hom.fiberIntegral :
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    Filter.TendstoCofinite (fun x : X ↦ f x) → (X → ℤ) → Y → ℤ)

#check (AlgebraicGeometry.Scheme.Hom.fiberIntegral_apply :
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
      (hf : Filter.TendstoCofinite (fun x : X ↦ f x)) (w : X → ℤ) (y : Y),
    f.fiberIntegral hf w y =
      ((Filter.tendstoCofinite_iff_finite_preimage_singleton (fun x : X ↦ f x)).mp hf y).toFinset.sum
        (fun x ↦ w x *
          (Field.finSepDegree (Y.residueField (f x)) (X.residueField x) : ℤ)))

end AlgebraicGeometry.Scheme.Hom
