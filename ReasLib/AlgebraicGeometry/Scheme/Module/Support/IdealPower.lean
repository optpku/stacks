/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.IdealPower.Product
public import ReasLib.AlgebraicGeometry.Scheme.Module.Support
public import ReasLib.RingTheory.Module.Support.IdealPower

/-!
# Support and ideal-power annihilation for scheme modules

This file relates vanishing of the product of a scheme module by a power of an ideal sheaf to
containment of the module's support in the ideal sheaf's closed support.
-/

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- A scheme module is uniformly annihilated on affine opens by a power of an ideal sheaf when
one exponent annihilates its module of sections over every affine open. -/
def IsAnnihilatedByIdealPowerOnAffineOpens
    (I : X.IdealSheafData) (ℱ : X.Modules) : Prop :=
  ∃ n : ℕ, ∀ U : X.affineOpens,
    I.ideal U ^ n • (⊤ : Submodule Γ(X, U.1) (Γ(ℱ, U.1))) = ⊥

/-- Uniform ideal-power annihilation on affine opens is equivalent to a uniform containment in
the annihilators of all affine-open section modules. -/
theorem isAnnihilatedByIdealPowerOnAffineOpens_iff_pow_le_annihilator
    (I : X.IdealSheafData) (ℱ : X.Modules) :
    IsAnnihilatedByIdealPowerOnAffineOpens I ℱ ↔
      ∃ n : ℕ, ∀ U : X.affineOpens,
        I.ideal U ^ n ≤ Module.annihilator (Γ(X, U.1)) (Γ(ℱ, U.1)) := sorry

namespace IsAnnihilatedByIdealPowerOnAffineOpens

/-- For a quasicoherent scheme module, uniform ideal-power annihilation on affine opens is
equivalent to the vanishing of one ideal-power product subobject. -/
theorem iff_exists_product_eq_bot
    (I : X.IdealSheafData) (ℱ : X.Modules) [ℱ.IsQuasicoherent] :
    IsAnnihilatedByIdealPowerOnAffineOpens I ℱ ↔
      ∃ n : ℕ, idealPowerProductSubobject I ℱ n = ⊥ := sorry

end IsAnnihilatedByIdealPowerOnAffineOpens

/-- A coherent module on a Noetherian scheme is annihilated by some power of an ideal sheaf if
and only if its support is contained in the closed support of the ideal sheaf. -/
theorem exists_idealPowerProductSubobject_eq_bot_iff_moduleSupport_subset
    [IsNoetherian X] (ℱ : X.Modules) [ℱ.IsCoherent] (I : X.IdealSheafData) :
    (∃ n : ℕ, idealPowerProductSubobject I ℱ n = ⊥) ↔
      RingedSpace.moduleSupport ℱ ⊆ (I.support : Set X) := sorry

end AlgebraicGeometry.Scheme.Modules
