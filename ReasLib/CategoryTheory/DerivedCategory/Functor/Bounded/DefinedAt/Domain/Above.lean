/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.DefinedAt.Naturality
public import ReasLib.CategoryTheory.Functor.Derived.DefinedAt.Functor
import Mathlib.Tactic.CrossRefAttribute

/-!
# Bounded-above comparison on the ambient source-defined domain

For a fixed additive functor, the bounded-above homotopy objects at which the ambient
left-derived diagram is essentially constant form a canonical full subcategory.  On this common
domain the bounded and ambient pointwise-value constructions are functors and their objectwise
comparisons assemble into a natural isomorphism.
-/

@[expose] public section

open CategoryTheory ComplexShape

noncomputable section

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor.LeftDerived.Value.BoundedAbove

variable {A : Type u₁} {B : Type u₂}
  [Category.{v₁} A] [Category.{v₂} B]
  [Abelian A] [Abelian B] [HasDerivedCategory.{w} B]

/-- The property of bounded-above homotopy objects where the ambient left-derived diagram is
essentially constant. -/
@[stacks 05T5 "ambient source-defined bounded-above objects"]
abbrev objects (F : A ⥤ B) [F.Additive] : ObjectProperty (HomotopyCategory.Minus A) :=
  (LeftDerived.DefinedAt.objects (Functor.Homotopy.toDerived F)
    (HomotopyCategory.quasiIso A (up ℤ))).inverseImage (HomotopyCategory.Minus.ι A)

/-- The full subcategory of ambient source-defined bounded-above homotopy objects. -/
@[stacks 05T5 "ambient source-defined bounded-above domain"]
abbrev Domain (F : A ⥤ B) [F.Additive] := (objects F).FullSubcategory

/-- A bounded-above source-defined object, viewed in the common comparison domain.  This is the
explicit reverse-transport entry point; no reverse typeclass instance is registered. -/
@[stacks 05T5 "bounded-above source-defined object in the comparison domain"]
noncomputable def Domain.ofBounded (F : A ⥤ B) [F.Additive]
    (K : HomotopyCategory.Minus A)
    [LeftDerived.DefinedAt F.toBoundedAboveDerived
      (HomotopyCategory.Minus.quasiIso A) K] : Domain F :=
  ⟨K, LeftDerived.DefinedAt.ofBoundedAbove F K⟩

/-- A morphism between bounded-above source-defined objects, viewed as a morphism in the common
comparison domain. -/
@[stacks 05T5 "bounded-above source-defined morphism in the comparison domain"]
def Domain.homOfBounded (F : A ⥤ B) [F.Additive]
    {K L : HomotopyCategory.Minus A} (f : K ⟶ L)
    [LeftDerived.DefinedAt F.toBoundedAboveDerived
      (HomotopyCategory.Minus.quasiIso A) K]
    [LeftDerived.DefinedAt F.toBoundedAboveDerived
      (HomotopyCategory.Minus.quasiIso A) L] :
    Domain.ofBounded F K ⟶ Domain.ofBounded F L := ObjectProperty.homMk f

/-- An object of the common bounded-above domain supplies its ambient source-definedness. -/
instance Domain.ambientDefinedAt (F : A ⥤ B) [F.Additive] (K : Domain F) :
    LeftDerived.DefinedAt (Functor.Homotopy.toDerived F)
      (HomotopyCategory.quasiIso A (up ℤ)) K.obj.obj := sorry

/-- Every object of the common domain is also source-defined for the bounded-above
presentation. -/
@[stacks 05T5 "bounded-above source-definedness on the comparison domain"]
theorem Domain.boundedDefinedAt (F : A ⥤ B) [F.Additive] (K : Domain F) :
    LeftDerived.DefinedAt F.toBoundedAboveDerived
      (HomotopyCategory.Minus.quasiIso A) K.obj := sorry

/-- The common comparison domain mapped to the bounded-above source-definedness domain. -/
@[stacks 05T5 "bounded-above source-defined-domain restriction"]
def Domain.toBounded (F : A ⥤ B) [F.Additive] :
    Domain F ⥤ LeftDerived.DefinedAt.Domain F.toBoundedAboveDerived
      (HomotopyCategory.Minus.quasiIso A) :=
  (LeftDerived.DefinedAt.objects F.toBoundedAboveDerived
    (HomotopyCategory.Minus.quasiIso A)).lift (objects F).ι
      (Domain.boundedDefinedAt F)

/-- The common comparison domain mapped to the ambient source-definedness domain. -/
@[stacks 05T5 "ambient source-defined-domain restriction for bounded-above objects"]
def Domain.toAmbient (F : A ⥤ B) [F.Additive] :
    Domain F ⥤ LeftDerived.DefinedAt.Domain (Functor.Homotopy.toDerived F)
      (HomotopyCategory.quasiIso A (up ℤ)) :=
  (LeftDerived.DefinedAt.objects (Functor.Homotopy.toDerived F)
    (HomotopyCategory.quasiIso A (up ℤ))).lift
      ((objects F).ι ⋙ HomotopyCategory.Minus.ι A) (Domain.ambientDefinedAt F)

namespace Domain.toBounded

/-- Restriction to the bounded source-definedness domain retains the underlying object. -/
@[simp]
theorem obj_obj (F : A ⥤ B) [F.Additive] (K : Domain F) :
    ((Domain.toBounded F).obj K).obj = K.obj := sorry

/-- Restriction to the bounded source-definedness domain retains the underlying morphism. -/
@[simp]
theorem map_hom (F : A ⥤ B) [F.Additive]
    {K L : Domain F} (f : K ⟶ L) :
    ((Domain.toBounded F).map f).hom = f.hom := sorry

end Domain.toBounded

namespace Domain.toAmbient

/-- Restriction to the ambient source-definedness domain applies the bounded-above inclusion. -/
@[simp]
theorem obj_obj (F : A ⥤ B) [F.Additive] (K : Domain F) :
    ((Domain.toAmbient F).obj K).obj = K.obj.obj := sorry

/-- Restriction to the ambient source-definedness domain retains the underlying ambient
morphism. -/
@[simp]
theorem map_hom (F : A ⥤ B) [F.Additive]
    {K L : Domain F} (f : K ⟶ L) :
    ((Domain.toAmbient F).map f).hom = f.hom.hom := sorry

end Domain.toAmbient

/-- The bounded-above pointwise left-derived values, viewed in the ambient derived category,
on the common source-defined domain. -/
@[stacks 05T5 "bounded-above value functor on the ambient source-defined domain"]
noncomputable def boundedFunctor (F : A ⥤ B) [F.Additive] : Domain F ⥤ DerivedCategory B :=
  Domain.toBounded F ⋙
    LeftDerived.DefinedAt.functor F.toBoundedAboveDerived
      (HomotopyCategory.Minus.quasiIso A) ⋙ DerivedCategory.Minus.ι

/-- The ambient pointwise left-derived values restricted to the common bounded-above
source-defined domain. -/
@[stacks 05T5 "ambient value functor on the bounded-above source-defined domain"]
noncomputable def ambientFunctor (F : A ⥤ B) [F.Additive] : Domain F ⥤ DerivedCategory B :=
  Domain.toAmbient F ⋙
    LeftDerived.DefinedAt.functor (Functor.Homotopy.toDerived F)
      (HomotopyCategory.quasiIso A (up ℤ))

namespace natIso

/-- Naturality of the bounded/unbounded value comparison on the common bounded-above domain. -/
@[stacks 05T5 "bounded-above source-defined-domain comparison naturality"]
theorem naturality (F : A ⥤ B) [F.Additive]
    {K L : Domain F} (f : K ⟶ L) :
    (boundedFunctor F).map f ≫
        (LeftDerived.Value.boundedAboveIso F L.obj).hom =
      (LeftDerived.Value.boundedAboveIso F K.obj).hom ≫
        (ambientFunctor F).map f := sorry

end natIso

/-- Stacks 05T5: bounded and ambient left-derived values agree naturally on the full
subcategory of ambient source-defined bounded-above objects. -/
@[stacks 05T5 "bounded-above comparison on the source-defined domain"]
noncomputable def natIso (F : A ⥤ B) [F.Additive] :
    boundedFunctor F ≅ ambientFunctor F :=
  NatIso.ofComponents (fun K => LeftDerived.Value.boundedAboveIso F K.obj)
    (fun f => natIso.naturality F f)

/-- The bounded/ambient value comparison at an object known only through bounded-above
source-definedness.  It avoids installing a reverse `DefinedAt` instance at the call site. -/
@[stacks 05T5 "value comparison from bounded-above source-definedness"]
noncomputable def isoOfBounded (F : A ⥤ B) [F.Additive]
    (K : HomotopyCategory.Minus A)
    [LeftDerived.DefinedAt F.toBoundedAboveDerived
      (HomotopyCategory.Minus.quasiIso A) K] :
    (boundedFunctor F).obj (Domain.ofBounded F K) ≅
      (ambientFunctor F).obj (Domain.ofBounded F K) :=
  (natIso F).app (Domain.ofBounded F K)

namespace natIso

/-- The forward component of the common-domain comparison is the canonical objectwise
bounded-above comparison. -/
@[simp, stacks 05T5 "bounded-above source-defined-domain comparison component"]
theorem hom_app (F : A ⥤ B) [F.Additive] (K : Domain F) :
    (natIso F).hom.app K = (LeftDerived.Value.boundedAboveIso F K.obj).hom := sorry

/-- The inverse component of the common-domain comparison is the inverse canonical objectwise
bounded-above comparison. -/
@[simp, stacks 05T5 "inverse bounded-above source-defined-domain comparison component"]
theorem inv_app (F : A ⥤ B) [F.Additive] (K : Domain F) :
    (natIso F).inv.app K = (LeftDerived.Value.boundedAboveIso F K.obj).inv := sorry

end natIso

namespace boundedFunctor

/-- The bounded-value functor evaluates to the included bounded pointwise value. -/
@[simp]
theorem obj (F : A ⥤ B) [F.Additive] (K : Domain F) :
    (boundedFunctor F).obj K = DerivedCategory.Minus.ι.obj
      (LeftDerived.Value.obj F.toBoundedAboveDerived
        (HomotopyCategory.Minus.quasiIso A) K.obj) := sorry

/-- The bounded-value functor maps by the included bounded pointwise-value map. -/
@[simp]
theorem map (F : A ⥤ B) [F.Additive]
    {K L : Domain F} (f : K ⟶ L) :
    (boundedFunctor F).map f = DerivedCategory.Minus.ι.map
      (LeftDerived.Value.map F.toBoundedAboveDerived
        (HomotopyCategory.Minus.quasiIso A) f.hom) := sorry

end boundedFunctor

namespace ambientFunctor

/-- The ambient-value functor evaluates to the ambient pointwise value. -/
@[simp]
theorem obj (F : A ⥤ B) [F.Additive] (K : Domain F) :
    (ambientFunctor F).obj K = LeftDerived.Value.obj (Functor.Homotopy.toDerived F)
      (HomotopyCategory.quasiIso A (up ℤ)) K.obj.obj := sorry

/-- The ambient-value functor maps by the ambient pointwise-value map. -/
@[simp]
theorem map (F : A ⥤ B) [F.Additive]
    {K L : Domain F} (f : K ⟶ L) :
    (ambientFunctor F).map f = LeftDerived.Value.map (Functor.Homotopy.toDerived F)
      (HomotopyCategory.quasiIso A (up ℤ)) f.hom.hom := sorry

end ambientFunctor

end CategoryTheory.Functor.LeftDerived.Value.BoundedAbove
