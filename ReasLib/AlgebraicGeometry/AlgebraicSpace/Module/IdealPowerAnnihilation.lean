/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.IdealPower

/-!
# Ideal-power annihilation of module sheaves

Annihilation by an ideal power is vanishing of the corresponding ideal-power
product subobject. A morphism has ideal-power-torsion kernel and cokernel when
one positive power annihilates both.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- A module is annihilated by `I^n` when the product subobject `I^n F` is zero. -/
def IsAnnihilatedByIdealPower (I : IdealSubobject X) (F : X.Modules) (n : ℕ) :
    Prop :=
  idealPowerProductSubobject I F n = ⊥

/-- Annihilation by `I^n` is vanishing of the product subobject `I^n F`. -/
theorem isAnnihilatedByIdealPower_iff (I : IdealSubobject X) (F : X.Modules)
    (n : ℕ) :
    IsAnnihilatedByIdealPower I F n ↔
      idealPowerProductSubobject I F n = ⊥ :=
  Iff.rfl


/-- A morphism of `𝒪_X`-modules has kernel and cokernel annihilated by a
positive power of an ideal sheaf. -/
def HasIdealPowerTorsionKernelCokernel (I : IdealSubobject X) {F G : X.Modules}
    (f : F ⟶ G) : Prop :=
  ∃ t : ℕ, 1 ≤ t ∧
    IsAnnihilatedByIdealPower I (kernel f) t ∧
      IsAnnihilatedByIdealPower I (cokernel f) t

/-- Kernel-and-cokernel ideal-power torsion is the existence of a positive power
annihilating both the kernel and the cokernel. -/
theorem hasIdealPowerTorsionKernelCokernel_iff (I : IdealSubobject X)
    {F G : X.Modules} (f : F ⟶ G) :
    HasIdealPowerTorsionKernelCokernel I f ↔
      ∃ t : ℕ, 1 ≤ t ∧
        IsAnnihilatedByIdealPower I (kernel f) t ∧
          IsAnnihilatedByIdealPower I (cokernel f) t :=
  Iff.rfl


end AlgebraicGeometry.AlgebraicSpace.Modules
