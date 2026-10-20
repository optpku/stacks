/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Blowup.TwistingSheaf

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.IsBlowup

#check (exceptionalIdeal :
  ∀ {A : Type u} [CommRing A] (I : Ideal A) {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of A)), X.IdealSheafData)

#check (exceptionalIdeal_def :
  ∀ {A : Type u} [CommRing A] (I : Ideal A) {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of A)),
      exceptionalIdeal I p = (Scheme.idealSheafDataOfIdealOnSpec I).comap p)

#check (twistingSheaf :
  ∀ {A : Type u} [CommRing A] (I : Ideal A) {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of A))
    [IsBlowup p (Scheme.idealSheafDataOfIdealOnSpec I)] (q : ℤ), X.Modules)

#check (twistingSheaf_def :
  ∀ {A : Type u} [CommRing A] (I : Ideal A) {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of A))
    [IsBlowup p (Scheme.idealSheafDataOfIdealOnSpec I)] (q : ℤ),
      twistingSheaf I p q =
        Scheme.Modules.tensorPowerInt (exceptionalIdeal I p).toModule q)

#check (twistingSheaf_one :
  ∀ {A : Type u} [CommRing A] (I : Ideal A) {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of A))
    [IsBlowup p (Scheme.idealSheafDataOfIdealOnSpec I)],
      CategoryTheory.IsIsomorphic
        (twistingSheaf I p 1) (exceptionalIdeal I p).toModule)

#check (thickenedTwistingSheaf :
  ∀ {A : Type u} [CommRing A] (I : Ideal A) {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of A))
    [IsBlowup p (Scheme.idealSheafDataOfIdealOnSpec I)] (n : ℕ) (q : ℤ), X.Modules)

#check (thickenedTwistingSheaf_def :
  ∀ {A : Type u} [CommRing A] (I : Ideal A) {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of A))
    [IsBlowup p (Scheme.idealSheafDataOfIdealOnSpec I)] (n : ℕ) (q : ℤ),
      thickenedTwistingSheaf I p n q =
        SheafOfModules.RingedSite.IdealSheaf.PowerQuotientModule.stage.{u, u, u}
          (exceptionalIdeal I p).toSubobject (twistingSheaf I p q) n)

end AlgebraicGeometry.IsBlowup
