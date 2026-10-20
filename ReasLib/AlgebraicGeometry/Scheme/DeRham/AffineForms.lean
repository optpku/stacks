/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Limits
public import ReasLib.AlgebraicGeometry.RingedSpace.DeRham

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AbsoluteDeRham

/-- The absolute one-form `b₀ db₁` on the top open of `Spec A`. -/
noncomputable def basicOneForm (A : Type u) [CommRing A] (b₀ b₁ : A) :
    (RingedSpace.DeRham.term
      (terminal.from (Spec (CommRingCat.of A))).toLRSHom.toShHom 1).val.obj
        (Opposite.op ⊤) :=
  TopCat.Sheaf.DeRham.basic
    (RingedSpace.DeRham.structureMap
      (terminal.from (Spec (CommRingCat.of A))).toLRSHom.toShHom)
    1 (Opposite.op ⊤) ((Scheme.ΓSpecIso (CommRingCat.of A)).inv b₀)
      (fun _ ↦ (Scheme.ΓSpecIso (CommRingCat.of A)).inv b₁)

/-- `basicOneForm A b₀ b₁` is the canonical affine section representing `b₀ db₁`. -/
theorem basicOneForm_apply (A : Type u) [CommRing A] (b₀ b₁ : A) :
    basicOneForm A b₀ b₁ =
      TopCat.Sheaf.DeRham.basic
        (RingedSpace.DeRham.structureMap
          (terminal.from (Spec (CommRingCat.of A))).toLRSHom.toShHom)
        1 (Opposite.op ⊤) ((Scheme.ΓSpecIso (CommRingCat.of A)).inv b₀)
          (fun _ ↦ (Scheme.ΓSpecIso (CommRingCat.of A)).inv b₁) := rfl

end AbsoluteDeRham

