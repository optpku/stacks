/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

variable {R : CommRingCat.{u}} {S : ShortComplex (Spec R).Modules}
variable (hS : S.ShortExact)
variable (h₁ : S.X₁.IsQuasicoherent) (h₂ : S.X₂.IsQuasicoherent)
variable (h₃ : S.X₃.IsQuasicoherent)

/- Lemma 26.7.8: in a short exact sequence of modules on the affine scheme `Spec R`,
quasi-coherence of any two terms implies quasi-coherence of the third. The source-facing checks
specialize the reusable two-out-of-three API to `Spec R`. -/
@[stacks 01IE] #check
  ObjectProperty.IsWeakSerreClass.prop_X₃_of_shortExact
    (Scheme.quasiCoherentModuleProperty (Spec R)) hS h₁ h₂
#check
  ObjectProperty.IsWeakSerreClass.prop_X₂_of_shortExact
    (Scheme.quasiCoherentModuleProperty (Spec R)) hS h₁ h₃
#check
  ObjectProperty.IsWeakSerreClass.prop_X₁_of_shortExact
    (Scheme.quasiCoherentModuleProperty (Spec R)) hS h₂ h₃

/- Generic companion owner for arbitrary schemes. -/
#check ObjectProperty.IsWeakSerreClass.prop_X₃_of_shortExact
