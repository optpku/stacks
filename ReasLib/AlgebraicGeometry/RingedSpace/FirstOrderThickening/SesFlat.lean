/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.CommSq
public import ReasLib.AlgebraicGeometry.RingedSpace.FirstOrderThickening.Complex
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.FlatMorphism
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.FlatOver
public import ReasLib.AlgebraicGeometry.RingedSpace.Morphism.Thickening.Strict

/-!
# Short exact sequences of flat first-order thickenings

This module records a three-column diagram of first-order thickenings with
short exact rows, strict flat vertical maps, and a relatively flat middle
module.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.IsFirstOrderThickening

/-- A three-column diagram of first-order thickenings along `f`, with short exact
rows, strict flat vertical maps, and a module flat over the middle base. -/
structure SesFlatThickenings
    {X S X1 X2 X3 S1 S2 S3 : RingedSpace.{u}}
    (f : X ⟶ S) (i1 : X ⟶ X1) (i2 : X ⟶ X2) (i3 : X ⟶ X3)
    (t1 : S ⟶ S1) (t2 : S ⟶ S2) (t3 : S ⟶ S3)
    [IsFirstOrderThickening i1] [IsFirstOrderThickening i2]
    [IsFirstOrderThickening i3] [IsFirstOrderThickening t1]
    [IsFirstOrderThickening t2] [IsFirstOrderThickening t3] where
  /-- The first morphism in the top row. -/
  h : Hom i1 i2
  /-- The second morphism in the top row. -/
  k : Hom i2 i3
  /-- The first morphism in the bottom row. -/
  base : Hom t1 t2
  /-- The second morphism in the bottom row. -/
  base' : Hom t2 t3
  /-- The first vertical morphism of the diagram. -/
  f1' : X1 ⟶ S1
  /-- The middle vertical morphism of the diagram. -/
  f2' : X2 ⟶ S2
  /-- The third vertical morphism of the diagram. -/
  f3' : X3 ⟶ S3
  /-- The first vertical morphism restricts to `f`. -/
  comm1 : i1 ≫ f1' = f ≫ t1
  /-- The middle vertical morphism restricts to `f`. -/
  comm2 : i2 ≫ f2' = f ≫ t2
  /-- The third vertical morphism restricts to `f`. -/
  comm3 : i3 ≫ f3' = f ≫ t3
  /-- The left square of the thickened diagram commutes. -/
  comm_thick : h.hom ≫ f2' = f1' ≫ base.hom
  /-- The right square of the thickened diagram commutes. -/
  comm_thick' : k.hom ≫ f3' = f2' ≫ base'.hom
  /-- The top row is a complex. -/
  top_isComplex : IsComplex h k
  /-- The induced top ideal row is short exact. -/
  top_shortExact : (idealSheafShortComplex h k top_isComplex).ShortExact
  /-- The bottom row is short exact. -/
  bot_ses : IsShortExact base base'
  /-- The first vertical pair is strict. -/
  strict1 : Thickening.Hom.IsStrict
    (Thickening.homMk f f1' comm1.symm : Thickening.of i1 ⟶ Thickening.of t1)
  /-- The middle vertical pair is strict. -/
  strict2 : Thickening.Hom.IsStrict
    (Thickening.homMk f f2' comm2.symm : Thickening.of i2 ⟶ Thickening.of t2)
  /-- The third vertical pair is strict. -/
  strict3 : Thickening.Hom.IsStrict
    (Thickening.homMk f f3' comm3.symm : Thickening.of i3 ⟶ Thickening.of t3)
  /-- The first vertical morphism is flat. -/
  flat1 : RingedSpace.Hom.IsFlat f1'
  /-- The middle vertical morphism is flat. -/
  flat2 : RingedSpace.Hom.IsFlat f2'
  /-- The third vertical morphism is flat. -/
  flat3 : RingedSpace.Hom.IsFlat f3'
  /-- The module on the middle thickening. -/
  module : X2.Modules
  /-- The middle module is flat over the middle base. -/
  module_isFlatOver : SheafOfModules.IsFlatOver module f2'

namespace SesFlatThickenings

variable {X S X1 X2 X3 S1 S2 S3 : RingedSpace.{u}}
variable {f : X ⟶ S} {i1 : X ⟶ X1} {i2 : X ⟶ X2} {i3 : X ⟶ X3}
variable {t1 : S ⟶ S1} {t2 : S ⟶ S2} {t3 : S ⟶ S3}
variable [IsFirstOrderThickening i1] [IsFirstOrderThickening i2]
variable [IsFirstOrderThickening i3] [IsFirstOrderThickening t1]
variable [IsFirstOrderThickening t2] [IsFirstOrderThickening t3]

/-- Assemble a short-exact flat first-order-thickening diagram from its data. -/
def of (h : Hom i1 i2) (k : Hom i2 i3) (base : Hom t1 t2) (base' : Hom t2 t3)
    (f1' : X1 ⟶ S1) (f2' : X2 ⟶ S2) (f3' : X3 ⟶ S3)
    (comm1 : i1 ≫ f1' = f ≫ t1) (comm2 : i2 ≫ f2' = f ≫ t2)
    (comm3 : i3 ≫ f3' = f ≫ t3)
    (comm_thick : h.hom ≫ f2' = f1' ≫ base.hom)
    (comm_thick' : k.hom ≫ f3' = f2' ≫ base'.hom)
    (top_isComplex : IsComplex h k)
    (top_shortExact : (idealSheafShortComplex h k top_isComplex).ShortExact)
    (bot_ses : IsShortExact base base')
    (strict1 : Thickening.Hom.IsStrict
      (Thickening.homMk f f1' comm1.symm : Thickening.of i1 ⟶ Thickening.of t1))
    (strict2 : Thickening.Hom.IsStrict
      (Thickening.homMk f f2' comm2.symm : Thickening.of i2 ⟶ Thickening.of t2))
    (strict3 : Thickening.Hom.IsStrict
      (Thickening.homMk f f3' comm3.symm : Thickening.of i3 ⟶ Thickening.of t3))
    (flat1 : RingedSpace.Hom.IsFlat f1') (flat2 : RingedSpace.Hom.IsFlat f2')
    (flat3 : RingedSpace.Hom.IsFlat f3')
    (module : X2.Modules) (module_isFlatOver : SheafOfModules.IsFlatOver module f2') :
    SesFlatThickenings f i1 i2 i3 t1 t2 t3 where
  h := h
  k := k
  base := base
  base' := base'
  f1' := f1'
  f2' := f2'
  f3' := f3'
  comm1 := comm1
  comm2 := comm2
  comm3 := comm3
  comm_thick := comm_thick
  comm_thick' := comm_thick'
  top_isComplex := top_isComplex
  top_shortExact := top_shortExact
  bot_ses := bot_ses
  strict1 := strict1
  strict2 := strict2
  strict3 := strict3
  flat1 := flat1
  flat2 := flat2
  flat3 := flat3
  module := module
  module_isFlatOver := module_isFlatOver

/-- The defining exactness, strictness, flatness, and relative-flatness facts. -/
theorem spec (S : SesFlatThickenings f i1 i2 i3 t1 t2 t3) :
    IsShortExact S.h S.k ∧ IsShortExact S.base S.base' ∧
      Thickening.Hom.IsStrict
        (Thickening.homMk f S.f1' S.comm1.symm : Thickening.of i1 ⟶ Thickening.of t1) ∧
      Thickening.Hom.IsStrict
        (Thickening.homMk f S.f2' S.comm2.symm : Thickening.of i2 ⟶ Thickening.of t2) ∧
      Thickening.Hom.IsStrict
        (Thickening.homMk f S.f3' S.comm3.symm : Thickening.of i3 ⟶ Thickening.of t3) ∧
      RingedSpace.Hom.IsFlat S.f1' ∧ RingedSpace.Hom.IsFlat S.f2' ∧
      RingedSpace.Hom.IsFlat S.f3' ∧
      SheafOfModules.IsFlatOver S.module S.f2' := sorry

/-- The three vertical morphisms restrict to the original morphism. -/
theorem restricts (S : SesFlatThickenings f i1 i2 i3 t1 t2 t3) :
    CommSq i1 f S.f1' t1 ∧ CommSq i2 f S.f2' t2 ∧ CommSq i3 f S.f3' t3 := sorry

/-- The two squares between the thickened rows commute. -/
theorem thickenedSq (S : SesFlatThickenings f i1 i2 i3 t1 t2 t3) :
    CommSq S.h.hom S.f1' S.f2' S.base.hom ∧
      CommSq S.k.hom S.f2' S.f3' S.base'.hom := sorry

/-- The bundled morphism of thickenings formed by the first vertical pair. -/
def thickeningHom1 (S : SesFlatThickenings f i1 i2 i3 t1 t2 t3) :
    Thickening.of i1 ⟶ Thickening.of t1 :=
  Thickening.homMk f S.f1' S.comm1.symm

/-- The bundled morphism of thickenings formed by the middle vertical pair. -/
def thickeningHom2 (S : SesFlatThickenings f i1 i2 i3 t1 t2 t3) :
    Thickening.of i2 ⟶ Thickening.of t2 :=
  Thickening.homMk f S.f2' S.comm2.symm

/-- The bundled morphism of thickenings formed by the third vertical pair. -/
def thickeningHom3 (S : SesFlatThickenings f i1 i2 i3 t1 t2 t3) :
    Thickening.of i3 ⟶ Thickening.of t3 :=
  Thickening.homMk f S.f3' S.comm3.symm

/-- The pullback of the stored middle module to the original space. -/
noncomputable def moduleRestrict (S : SesFlatThickenings f i1 i2 i3 t1 t2 t3) :
    X.Modules :=
  (i2 ^*).obj S.module

/-- The canonical splitting of the first inclusion supplied by the top complex. -/
noncomputable def canonicalSplitting
    [HasWeakSheafify (Opens.grothendieckTopology X3) CommRingCat.{u}]
    [(Opens.grothendieckTopology X3).WEqualsLocallyBijective CommRingCat.{u}]
    (S : SesFlatThickenings f i1 i2 i3 t1 t2 t3) : X1 ⟶ X :=
  canonicalTrivialization S.h S.k S.top_isComplex

/-- The canonical splitting is a left inverse of the first inclusion. -/
theorem canonicalSplitting_leftInv
    [HasWeakSheafify (Opens.grothendieckTopology X3) CommRingCat.{u}]
    [(Opens.grothendieckTopology X3).WEqualsLocallyBijective CommRingCat.{u}]
    (S : SesFlatThickenings f i1 i2 i3 t1 t2 t3) :
    i1 ≫ canonicalSplitting S = 𝟙 X := sorry

/-- The top row of the diagram is short exact. -/
theorem top_isShortExact (S : SesFlatThickenings f i1 i2 i3 t1 t2 t3) :
    IsShortExact S.h S.k := sorry

end SesFlatThickenings

end AlgebraicGeometry.RingedSpace.IsFirstOrderThickening
