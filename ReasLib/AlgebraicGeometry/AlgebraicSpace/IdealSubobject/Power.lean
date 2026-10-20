module

public import Mathlib.RingTheory.Ideal.Operations
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.IdealQuotient
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.IdealPower
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IdealSubobject.Product

/-!
# Powers of ideal sheaves on algebraic spaces

Ideal powers are iterated images of the ideal-sheaf action on the structure module.
Vanishing of a fixed power of an ideal sheaf is expressed uniformly on the
objects of the small étale site.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The `n`th power of an ideal sheaf vanishes if it vanishes on every object of
the small étale site. -/
def IdealSubobject.pow_eq_bot {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) (n : ℕ) : Prop :=
  ∀ (U : (smallEtaleSite X)ᵒᵖ),
    IdealSheaf.sections (Modules.toCommSubobject I) U ^ n = ⊥

/-- Vanishing of the `n`th power of an ideal sheaf is sectionwise vanishing on the
small étale site. -/
theorem IdealSubobject.pow_eq_bot_iff {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) (n : ℕ) :
    I.pow_eq_bot n ↔
      ∀ (U : (smallEtaleSite X)ᵒᵖ),
        IdealSheaf.sections (Modules.toCommSubobject I) U ^ n = ⊥ :=
  sorry

namespace IdealSubobject

/-- The `n`th power of an ideal subobject of `𝒪_X`, as the ideal-power product
with the structure module. -/
noncomputable def pow {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) (n : ℕ) : IdealSubobject X :=
  Modules.idealPowerProductSubobject I (SheafOfModules.unit (structureSheaf X)) n

/-- The `n`th power of an ideal subobject is the ideal-power product against
the structure module. -/
theorem pow_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) (n : ℕ) :
    I.pow n =
      Modules.idealPowerProductSubobject I
        (SheafOfModules.unit (structureSheaf X)) n :=
  rfl

/-- The zeroth power of an ideal subobject is the unit ideal. -/
theorem pow_zero {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) : I.pow 0 = ⊤ :=
  rfl

/-- The successor power of an ideal subobject is the product with the previous
power. -/
theorem pow_succ {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) (n : ℕ) :
    I.pow (n + 1) = IdealSubobject.mul I (I.pow n) :=
  rfl

/-- The product of two powers of an ideal subobject is the power of the sum of
the exponents. -/
theorem mul_pow_add {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) (n m : ℕ) :
    IdealSubobject.mul (I.pow n) (I.pow m) = I.pow (n + m) :=
  sorry

end IdealSubobject

/-- Natural-number powers of ideal subobjects of `𝒪_X`. -/
instance instPowIdealSubobject {S : Scheme.{u}} {X : AlgebraicSpace S} :
    Pow (IdealSubobject X) ℕ where
  pow := IdealSubobject.pow

namespace IsQuasiCoherent

/-- Powers of a quasi-coherent ideal sheaf are quasi-coherent. -/
instance instIsQuasiCoherent_pow {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) [IsQuasiCoherent I] (n : ℕ) :
    IsQuasiCoherent (I.pow n) :=
  sorry

/-- Natural-number powers of a quasi-coherent ideal sheaf are quasi-coherent. -/
instance instIsQuasiCoherent_powNotation {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) [IsQuasiCoherent I] (n : ℕ) :
    IsQuasiCoherent (I ^ n) :=
  instIsQuasiCoherent_pow I n

end IsQuasiCoherent

end AlgebraicGeometry.AlgebraicSpace
