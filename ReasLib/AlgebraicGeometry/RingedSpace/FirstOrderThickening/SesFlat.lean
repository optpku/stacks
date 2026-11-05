/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.FirstOrderThickening.Conormal
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

/-- First-order, exactness, strictness and flatness properties of a chain and module.
The first-order fields are local instance binders inside this structure only;
no instances are registered for an arbitrary chain. -/
structure IsSesFlatThickening
    {X S X1 X2 X3 S1 S2 S3 : RingedSpace.{u}}
    (f : X ⟶ S) (i1 : X ⟶ X1) (i2 : X ⟶ X2) (i3 : X ⟶ X3)
    (t1 : S ⟶ S1) (t2 : S ⟶ S2) (t3 : S ⟶ S3)
    (C : ThickeningSquareChain f i1 i2 i3 t1 t2 t3) (module : X2.Modules) : Prop where
  /-- The inclusion `i1` is a first-order thickening. -/
  [firstOrder_i1 : IsFirstOrderThickening i1]
  /-- The inclusion `i2` is a first-order thickening. -/
  [firstOrder_i2 : IsFirstOrderThickening i2]
  /-- The inclusion `i3` is a first-order thickening. -/
  [firstOrder_i3 : IsFirstOrderThickening i3]
  /-- The inclusion `t1` is a first-order thickening. -/
  [firstOrder_t1 : IsFirstOrderThickening t1]
  /-- The inclusion `t2` is a first-order thickening. -/
  [firstOrder_t2 : IsFirstOrderThickening t2]
  /-- The inclusion `t3` is a first-order thickening. -/
  [firstOrder_t3 : IsFirstOrderThickening t3]
  /-- The top row is a complex. -/
  top_isComplex : IsComplex C.h C.k
  /-- The induced top ideal row is short exact. -/
  top_shortExact : (idealSheafShortComplex C.h C.k top_isComplex).ShortExact
  /-- The bottom row is short exact. -/
  bot_ses : IsShortExact C.base C.base'
  /-- The first vertical pair is strict. -/
  strict1 : Thickening.Hom.IsStrict
    (Thickening.homMk f C.f1' C.comm1.symm : Thickening.of i1 ⟶ Thickening.of t1)
  /-- The middle vertical pair is strict. -/
  strict2 : Thickening.Hom.IsStrict
    (Thickening.homMk f C.f2' C.comm2.symm : Thickening.of i2 ⟶ Thickening.of t2)
  /-- The third vertical pair is strict. -/
  strict3 : Thickening.Hom.IsStrict
    (Thickening.homMk f C.f3' C.comm3.symm : Thickening.of i3 ⟶ Thickening.of t3)
  /-- The first vertical morphism is flat. -/
  flat1 : RingedSpace.Hom.IsFlat C.f1'
  /-- The middle vertical morphism is flat. -/
  flat2 : RingedSpace.Hom.IsFlat C.f2'
  /-- The third vertical morphism is flat. -/
  flat3 : RingedSpace.Hom.IsFlat C.f3'
  /-- The middle module is flat over the middle base. -/
  module_isFlatOver : SheafOfModules.IsFlatOver module C.f2'

/-- Compatibility bundle of the commuting chain, middle module and properties. -/
structure SesFlatThickenings
    {X S X1 X2 X3 S1 S2 S3 : RingedSpace.{u}}
    (f : X ⟶ S) (i1 : X ⟶ X1) (i2 : X ⟶ X2) (i3 : X ⟶ X3)
    (t1 : S ⟶ S1) (t2 : S ⟶ S2) (t3 : S ⟶ S3)
    [IsFirstOrderThickening i1] [IsFirstOrderThickening i2]
    [IsFirstOrderThickening i3] [IsFirstOrderThickening t1]
    [IsFirstOrderThickening t2] [IsFirstOrderThickening t3] where
  /-- The underlying commuting chain. -/
  toThickeningSquareChain : ThickeningSquareChain f i1 i2 i3 t1 t2 t3
  /-- The module on the middle thickening. -/
  module : X2.Modules
  /-- The separated exactness, strictness and flatness properties. -/
  isSesFlat : IsSesFlatThickening f i1 i2 i3 t1 t2 t3 toThickeningSquareChain module

namespace SesFlatThickenings

variable {X S X1 X2 X3 S1 S2 S3 : RingedSpace.{u}}
variable {f : X ⟶ S} {i1 : X ⟶ X1} {i2 : X ⟶ X2} {i3 : X ⟶ X3}
variable {t1 : S ⟶ S1} {t2 : S ⟶ S2} {t3 : S ⟶ S3}
variable [IsFirstOrderThickening i1] [IsFirstOrderThickening i2]
variable [IsFirstOrderThickening i3] [IsFirstOrderThickening t1]
variable [IsFirstOrderThickening t2] [IsFirstOrderThickening t3]

/-- The stored row morphism, viewed as a morphism of first-order thickenings. -/
abbrev h (S : SesFlatThickenings f i1 i2 i3 t1 t2 t3) : Hom i1 i2 :=
  S.toThickeningSquareChain.h

/-- The stored row morphism, viewed as a morphism of first-order thickenings. -/
abbrev k (S : SesFlatThickenings f i1 i2 i3 t1 t2 t3) : Hom i2 i3 :=
  S.toThickeningSquareChain.k

/-- The stored row morphism, viewed as a morphism of first-order thickenings. -/
abbrev base (S : SesFlatThickenings f i1 i2 i3 t1 t2 t3) : Hom t1 t2 :=
  S.toThickeningSquareChain.base

/-- The stored row morphism, viewed as a morphism of first-order thickenings. -/
abbrev base' (S : SesFlatThickenings f i1 i2 i3 t1 t2 t3) : Hom t2 t3 :=
  S.toThickeningSquareChain.base'

/-- Compatibility accessor for a commuting thickened square. -/
abbrev comm_thick (S : SesFlatThickenings f i1 i2 i3 t1 t2 t3) :=
  S.toThickeningSquareChain.comm_thick

/-- Compatibility accessor for a commuting thickened square. -/
abbrev comm_thick' (S : SesFlatThickenings f i1 i2 i3 t1 t2 t3) :=
  S.toThickeningSquareChain.comm_thick'

/-- Compatibility accessor for the chain. -/
abbrev f1' (S : SesFlatThickenings f i1 i2 i3 t1 t2 t3) :=
  S.toThickeningSquareChain.f1'

/-- Compatibility accessor for the chain. -/
abbrev f2' (S : SesFlatThickenings f i1 i2 i3 t1 t2 t3) :=
  S.toThickeningSquareChain.f2'

/-- Compatibility accessor for the chain. -/
abbrev f3' (S : SesFlatThickenings f i1 i2 i3 t1 t2 t3) :=
  S.toThickeningSquareChain.f3'

/-- Compatibility accessor for the chain. -/
abbrev comm1 (S : SesFlatThickenings f i1 i2 i3 t1 t2 t3) :=
  S.toThickeningSquareChain.comm1

/-- Compatibility accessor for the chain. -/
abbrev comm2 (S : SesFlatThickenings f i1 i2 i3 t1 t2 t3) :=
  S.toThickeningSquareChain.comm2

/-- Compatibility accessor for the chain. -/
abbrev comm3 (S : SesFlatThickenings f i1 i2 i3 t1 t2 t3) :=
  S.toThickeningSquareChain.comm3

/-- Compatibility accessor for the separated property predicate. -/
abbrev top_isComplex (S : SesFlatThickenings f i1 i2 i3 t1 t2 t3) :=
  S.isSesFlat.top_isComplex

/-- Compatibility accessor for the separated property predicate. -/
abbrev top_shortExact (S : SesFlatThickenings f i1 i2 i3 t1 t2 t3) :=
  S.isSesFlat.top_shortExact

/-- Compatibility accessor for the separated property predicate. -/
abbrev bot_ses (S : SesFlatThickenings f i1 i2 i3 t1 t2 t3) :=
  S.isSesFlat.bot_ses

/-- Compatibility accessor for the separated property predicate. -/
abbrev strict1 (S : SesFlatThickenings f i1 i2 i3 t1 t2 t3) :=
  S.isSesFlat.strict1

/-- Compatibility accessor for the separated property predicate. -/
abbrev strict2 (S : SesFlatThickenings f i1 i2 i3 t1 t2 t3) :=
  S.isSesFlat.strict2

/-- Compatibility accessor for the separated property predicate. -/
abbrev strict3 (S : SesFlatThickenings f i1 i2 i3 t1 t2 t3) :=
  S.isSesFlat.strict3

/-- Compatibility accessor for the separated property predicate. -/
abbrev flat1 (S : SesFlatThickenings f i1 i2 i3 t1 t2 t3) :=
  S.isSesFlat.flat1

/-- Compatibility accessor for the separated property predicate. -/
abbrev flat2 (S : SesFlatThickenings f i1 i2 i3 t1 t2 t3) :=
  S.isSesFlat.flat2

/-- Compatibility accessor for the separated property predicate. -/
abbrev flat3 (S : SesFlatThickenings f i1 i2 i3 t1 t2 t3) :=
  S.isSesFlat.flat3

/-- Compatibility accessor for the separated property predicate. -/
abbrev module_isFlatOver (S : SesFlatThickenings f i1 i2 i3 t1 t2 t3) :=
  S.isSesFlat.module_isFlatOver

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
  toThickeningSquareChain := {
    h := h
    k := k
    base := base
    base' := base'
    vertical1 := Under.homMk f1' comm1
    vertical2 := Under.homMk f2' comm2
    vertical3 := Under.homMk f3' comm3
    comm_thick := comm_thick
    comm_thick' := comm_thick' }
  module := module
  isSesFlat := {
    firstOrder_i1 := inferInstance
    firstOrder_i2 := inferInstance
    firstOrder_i3 := inferInstance
    firstOrder_t1 := inferInstance
    firstOrder_t2 := inferInstance
    firstOrder_t3 := inferInstance
    top_isComplex := top_isComplex
    top_shortExact := top_shortExact
    bot_ses := bot_ses
    strict1 := strict1
    strict2 := strict2
    strict3 := strict3
    flat1 := flat1
    flat2 := flat2
    flat3 := flat3
    module_isFlatOver := module_isFlatOver }

/-- The defining exactness, strictness, flatness, and relative-flatness facts. -/
theorem spec (S : SesFlatThickenings f i1 i2 i3 t1 t2 t3) :
    IsShortExact S.h S.k ∧ IsShortExact S.base S.base' ∧
      Thickening.Hom.IsStrict
        (S.toThickeningSquareChain.thickeningHom1 : Thickening.of i1 ⟶ Thickening.of t1) ∧
      Thickening.Hom.IsStrict
        (S.toThickeningSquareChain.thickeningHom2 : Thickening.of i2 ⟶ Thickening.of t2) ∧
      Thickening.Hom.IsStrict
        (S.toThickeningSquareChain.thickeningHom3 : Thickening.of i3 ⟶ Thickening.of t3) ∧
      RingedSpace.Hom.IsFlat S.f1' ∧ RingedSpace.Hom.IsFlat S.f2' ∧
      RingedSpace.Hom.IsFlat S.f3' ∧
      SheafOfModules.IsFlatOver S.module S.f2' :=
  ⟨⟨S.top_isComplex, S.top_shortExact⟩, S.bot_ses, S.strict1, S.strict2,
    S.strict3, S.flat1, S.flat2, S.flat3, S.module_isFlatOver⟩

/-- The three vertical morphisms restrict to the original morphism. -/
theorem restricts (S : SesFlatThickenings f i1 i2 i3 t1 t2 t3) :
    CommSq i1 f S.f1' t1 ∧ CommSq i2 f S.f2' t2 ∧ CommSq i3 f S.f3' t3 :=
  S.toThickeningSquareChain.restricts

/-- The two squares between the thickened rows commute. -/
theorem thickenedSq (S : SesFlatThickenings f i1 i2 i3 t1 t2 t3) :
    CommSq S.h.hom S.f1' S.f2' S.base.hom ∧
      CommSq S.k.hom S.f2' S.f3' S.base'.hom :=
  S.toThickeningSquareChain.thickenedSq

/-- The bundled morphism of thickenings formed by the first vertical pair. -/
def thickeningHom1 (S : SesFlatThickenings f i1 i2 i3 t1 t2 t3) :
    Thickening.of i1 ⟶ Thickening.of t1 :=
  S.toThickeningSquareChain.thickeningHom1

/-- The bundled morphism of thickenings formed by the middle vertical pair. -/
def thickeningHom2 (S : SesFlatThickenings f i1 i2 i3 t1 t2 t3) :
    Thickening.of i2 ⟶ Thickening.of t2 :=
  S.toThickeningSquareChain.thickeningHom2

/-- The bundled morphism of thickenings formed by the third vertical pair. -/
def thickeningHom3 (S : SesFlatThickenings f i1 i2 i3 t1 t2 t3) :
    Thickening.of i3 ⟶ Thickening.of t3 :=
  S.toThickeningSquareChain.thickeningHom3

/-- The pullback of the stored middle module to the original space. -/
noncomputable def moduleRestrict (S : SesFlatThickenings f i1 i2 i3 t1 t2 t3) :
    X.Modules :=
  S.toThickeningSquareChain.moduleRestrict S.module

/-- The canonical splitting of the first inclusion supplied by the top complex. -/
noncomputable def canonicalSplitting
    [HasWeakSheafify (Opens.grothendieckTopology X3) CommRingCat.{u}]
    [(Opens.grothendieckTopology X3).WEqualsLocallyBijective CommRingCat.{u}]
    (S : SesFlatThickenings f i1 i2 i3 t1 t2 t3) : X1 ⟶ X :=
  S.toThickeningSquareChain.canonicalSplitting S.top_isComplex

/-- The canonical splitting is a left inverse of the first inclusion. -/
theorem canonicalSplitting_leftInv
    [HasWeakSheafify (Opens.grothendieckTopology X3) CommRingCat.{u}]
    [(Opens.grothendieckTopology X3).WEqualsLocallyBijective CommRingCat.{u}]
    (S : SesFlatThickenings f i1 i2 i3 t1 t2 t3) :
    i1 ≫ canonicalSplitting S = 𝟙 X :=
  S.toThickeningSquareChain.canonicalSplitting_leftInv S.top_isComplex

/-- The top row of the diagram is short exact. -/
theorem top_isShortExact (S : SesFlatThickenings f i1 i2 i3 t1 t2 t3) :
    IsShortExact S.h S.k := ⟨S.top_isComplex, S.top_shortExact⟩

end SesFlatThickenings

end AlgebraicGeometry.RingedSpace.IsFirstOrderThickening
