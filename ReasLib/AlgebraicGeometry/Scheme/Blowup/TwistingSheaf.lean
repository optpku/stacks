/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Ideal.PowerQuotient.Module
public import ReasLib.AlgebraicGeometry.Scheme.Blowup.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.IdealSheaf
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.Spec
public import ReasLib.AlgebraicGeometry.Scheme.Module.TensorPower

/-!
# Twisting sheaves on a blowup

This module defines the integral tensor powers of the exceptional ideal and their
ideal-power quotients.
-/

@[expose] public section

open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.IsBlowup

/-- The exceptional ideal on the blowup of `Spec A` in `I`. -/
noncomputable abbrev exceptionalIdeal
    {A : Type u} [CommRing A] (I : Ideal A) {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of A)) : X.IdealSheafData :=
  (Scheme.idealSheafDataOfIdealOnSpec I).comap p

/-- The exceptional ideal is the pullback of the ideal sheaf associated to `I`. -/
theorem exceptionalIdeal_def
    {A : Type u} [CommRing A] (I : Ideal A) {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of A)) :
    exceptionalIdeal I p = (Scheme.idealSheafDataOfIdealOnSpec I).comap p := sorry

/-- The twisting sheaf `𝒪_X(q)` on a blowup, as an integral tensor power of its exceptional ideal. -/
noncomputable def twistingSheaf
    {A : Type u} [CommRing A] (I : Ideal A) {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of A))
    [IsBlowup p (Scheme.idealSheafDataOfIdealOnSpec I)] (q : ℤ) : X.Modules :=
  Scheme.Modules.tensorPowerInt (exceptionalIdeal I p).toModule q

/-- The blowup twisting sheaf is the integral tensor power of the exceptional ideal. -/
theorem twistingSheaf_def
    {A : Type u} [CommRing A] (I : Ideal A) {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of A))
    [IsBlowup p (Scheme.idealSheafDataOfIdealOnSpec I)] (q : ℤ) :
    twistingSheaf I p q =
      Scheme.Modules.tensorPowerInt (exceptionalIdeal I p).toModule q := sorry

/-- The degree-one twisting sheaf is isomorphic to the exceptional ideal module. -/
theorem twistingSheaf_one
    {A : Type u} [CommRing A] (I : Ideal A) {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of A))
    [IsBlowup p (Scheme.idealSheafDataOfIdealOnSpec I)] :
    CategoryTheory.IsIsomorphic
      (twistingSheaf I p 1) (exceptionalIdeal I p).toModule := sorry

/-- The twist `𝒪_{Yₙ}(q)` on the `n`-th infinitesimal neighborhood of the exceptional divisor. -/
noncomputable def thickenedTwistingSheaf
    {A : Type u} [CommRing A] (I : Ideal A) {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of A))
    [IsBlowup p (Scheme.idealSheafDataOfIdealOnSpec I)]
    (n : ℕ) (q : ℤ) : X.Modules :=
  SheafOfModules.RingedSite.IdealSheaf.PowerQuotientModule.stage.{u, u, u}
    (exceptionalIdeal I p).toSubobject (twistingSheaf I p q) n

/-- The thickened twisting sheaf is the ideal-power quotient of the corresponding twisting sheaf. -/
theorem thickenedTwistingSheaf_def
    {A : Type u} [CommRing A] (I : Ideal A) {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of A))
    [IsBlowup p (Scheme.idealSheafDataOfIdealOnSpec I)]
    (n : ℕ) (q : ℤ) :
    thickenedTwistingSheaf I p n q =
      SheafOfModules.RingedSite.IdealSheaf.PowerQuotientModule.stage.{u, u, u}
        (exceptionalIdeal I p).toSubobject (twistingSheaf I p q) n := sorry

end AlgebraicGeometry.IsBlowup
