/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.RingTheory.PicardGroup
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Basic

/-!
# Affine invertibility of modules and associated sheaves

This leaf compares invertibility of an `R`-module with invertibility of `M^~` on `Spec R` and
provides the canonical affine global-sections instance.
-/

@[expose] public section

open AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- On `Spec R`, the associated sheaf `M^~` is invertible exactly when `M` is an invertible
`R`-module. -/
theorem tilde_invertible_iff_module_invertible {R : CommRingCat.{u}} (M : ModuleCat R) :
    Invertible (tilde M) ↔ Module.Invertible R M := sorry

/-- The associated sheaf of an invertible module is invertible. -/
instance instInvertibleTilde {R : CommRingCat.{u}} (M : ModuleCat R)
    [Module.Invertible R M] : Invertible (tilde M) := sorry

/-- The module of global sections of an invertible module on `Spec R` is invertible. -/
instance instInvertibleModuleSpecΓ {R : CommRingCat.{u}} (L : (Spec R).Modules)
    [Invertible L] : Module.Invertible R (moduleSpecΓFunctor.obj L) := sorry

end AlgebraicGeometry.Scheme.Modules
