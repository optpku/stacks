module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.DefinedAt.Naturality
public import ReasLib.CategoryTheory.Functor.Derived.DefinedAt.Functor
import Mathlib.Tactic.CrossRefAttribute

/-!
# Bounded-below comparison on the ambient source-defined domain

For a fixed additive functor, the bounded-below homotopy objects at which the ambient
right-derived diagram is essentially constant form a canonical full subcategory.  On this common
domain the bounded and ambient pointwise-value constructions are functors and their objectwise
comparisons assemble into a natural isomorphism.
-/

@[expose] public section

open CategoryTheory ComplexShape

noncomputable section

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor.RightDerived.Value.BoundedBelow

variable {A : Type u₁} {B : Type u₂}
  [Category.{v₁} A] [Category.{v₂} B]
  [Abelian A] [Abelian B] [HasDerivedCategory.{w} B]

/-- The property of bounded-below homotopy objects where the ambient right-derived diagram is
essentially constant. -/
@[stacks 05T5 "ambient source-defined bounded-below objects"]
abbrev objects (F : A ⥤ B) [F.Additive] : ObjectProperty (HomotopyCategory.Plus A) :=
  (RightDerived.DefinedAt.objects (Functor.Homotopy.toDerived F)
    (HomotopyCategory.quasiIso A (up ℤ))).inverseImage (HomotopyCategory.Plus.ι A)

/-- The full subcategory of ambient source-defined bounded-below homotopy objects. -/
@[stacks 05T5 "ambient source-defined bounded-below domain"]
abbrev Domain (F : A ⥤ B) [F.Additive] := (objects F).FullSubcategory

/-- A bounded-below source-defined object, viewed in the common comparison domain.  This is the
explicit reverse-transport entry point; no reverse typeclass instance is registered. -/
@[stacks 05T5 "bounded-below source-defined object in the comparison domain"]
noncomputable def Domain.ofBounded (F : A ⥤ B) [F.Additive]
    (K : HomotopyCategory.Plus A)
    [RightDerived.DefinedAt F.toBoundedBelowDerived
      (HomotopyCategory.Plus.quasiIso A) K] : Domain F :=
  ⟨K, RightDerived.DefinedAt.ofBoundedBelow F K⟩

/-- A morphism between bounded-below source-defined objects, viewed as a morphism in the common
comparison domain. -/
@[stacks 05T5 "bounded-below source-defined morphism in the comparison domain"]
def Domain.homOfBounded (F : A ⥤ B) [F.Additive]
    {K L : HomotopyCategory.Plus A} (f : K ⟶ L)
    [RightDerived.DefinedAt F.toBoundedBelowDerived
      (HomotopyCategory.Plus.quasiIso A) K]
    [RightDerived.DefinedAt F.toBoundedBelowDerived
      (HomotopyCategory.Plus.quasiIso A) L] :
    Domain.ofBounded F K ⟶ Domain.ofBounded F L := ObjectProperty.homMk f

/-- An object of the common bounded-below domain supplies its ambient source-definedness. -/
instance Domain.ambientDefinedAt (F : A ⥤ B) [F.Additive] (K : Domain F) :
    RightDerived.DefinedAt (Functor.Homotopy.toDerived F)
      (HomotopyCategory.quasiIso A (up ℤ)) K.obj.obj := sorry

/-- Every object of the common domain is also source-defined for the bounded-below
presentation. -/
@[stacks 05T5 "bounded-below source-definedness on the comparison domain"]
theorem Domain.boundedDefinedAt (F : A ⥤ B) [F.Additive] (K : Domain F) :
    RightDerived.DefinedAt F.toBoundedBelowDerived
      (HomotopyCategory.Plus.quasiIso A) K.obj := sorry

/-- The common comparison domain mapped to the bounded-below source-definedness domain. -/
@[stacks 05T5 "bounded-below source-defined-domain restriction"]
def Domain.toBounded (F : A ⥤ B) [F.Additive] :
    Domain F ⥤ RightDerived.DefinedAt.Domain F.toBoundedBelowDerived
      (HomotopyCategory.Plus.quasiIso A) :=
  (RightDerived.DefinedAt.objects F.toBoundedBelowDerived
    (HomotopyCategory.Plus.quasiIso A)).lift (objects F).ι
      (Domain.boundedDefinedAt F)

/-- The common comparison domain mapped to the ambient source-definedness domain. -/
@[stacks 05T5 "ambient source-defined-domain restriction for bounded-below objects"]
def Domain.toAmbient (F : A ⥤ B) [F.Additive] :
    Domain F ⥤ RightDerived.DefinedAt.Domain (Functor.Homotopy.toDerived F)
      (HomotopyCategory.quasiIso A (up ℤ)) :=
  (RightDerived.DefinedAt.objects (Functor.Homotopy.toDerived F)
    (HomotopyCategory.quasiIso A (up ℤ))).lift
      ((objects F).ι ⋙ HomotopyCategory.Plus.ι A) (Domain.ambientDefinedAt F)

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

/-- Restriction to the ambient source-definedness domain applies the bounded-below inclusion. -/
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

/-- The bounded-below pointwise right-derived values, viewed in the ambient derived category,
on the common source-defined domain. -/
@[stacks 05T5 "bounded-below value functor on the ambient source-defined domain"]
noncomputable def boundedFunctor (F : A ⥤ B) [F.Additive] : Domain F ⥤ DerivedCategory B :=
  Domain.toBounded F ⋙
    RightDerived.DefinedAt.functor F.toBoundedBelowDerived
      (HomotopyCategory.Plus.quasiIso A) ⋙ DerivedCategory.Plus.ι

/-- The ambient pointwise right-derived values restricted to the common bounded-below
source-defined domain. -/
@[stacks 05T5 "ambient value functor on the bounded-below source-defined domain"]
noncomputable def ambientFunctor (F : A ⥤ B) [F.Additive] : Domain F ⥤ DerivedCategory B :=
  Domain.toAmbient F ⋙
    RightDerived.DefinedAt.functor (Functor.Homotopy.toDerived F)
      (HomotopyCategory.quasiIso A (up ℤ))

namespace natIso

/-- Naturality of the bounded/unbounded value comparison on the common bounded-below domain. -/
@[stacks 05T5 "bounded-below source-defined-domain comparison naturality"]
theorem naturality (F : A ⥤ B) [F.Additive]
    {K L : Domain F} (f : K ⟶ L) :
    (boundedFunctor F).map f ≫
        (RightDerived.Value.boundedBelowIso F L.obj).hom =
      (RightDerived.Value.boundedBelowIso F K.obj).hom ≫
        (ambientFunctor F).map f := sorry

end natIso

/-- Stacks 05T5: bounded and ambient right-derived values agree naturally on the full
subcategory of ambient source-defined bounded-below objects. -/
@[stacks 05T5 "bounded-below comparison on the source-defined domain"]
noncomputable def natIso (F : A ⥤ B) [F.Additive] :
    boundedFunctor F ≅ ambientFunctor F :=
  NatIso.ofComponents (fun K => RightDerived.Value.boundedBelowIso F K.obj)
    (fun f => natIso.naturality F f)

/-- The bounded/ambient value comparison at an object known only through bounded-below
source-definedness.  It avoids installing a reverse `DefinedAt` instance at the call site. -/
@[stacks 05T5 "value comparison from bounded-below source-definedness"]
noncomputable def isoOfBounded (F : A ⥤ B) [F.Additive]
    (K : HomotopyCategory.Plus A)
    [RightDerived.DefinedAt F.toBoundedBelowDerived
      (HomotopyCategory.Plus.quasiIso A) K] :
    (boundedFunctor F).obj (Domain.ofBounded F K) ≅
      (ambientFunctor F).obj (Domain.ofBounded F K) :=
  (natIso F).app (Domain.ofBounded F K)

namespace natIso

/-- The forward component of the common-domain comparison is the canonical objectwise
bounded-below comparison. -/
@[simp, stacks 05T5 "bounded-below source-defined-domain comparison component"]
theorem hom_app (F : A ⥤ B) [F.Additive] (K : Domain F) :
    (natIso F).hom.app K = (RightDerived.Value.boundedBelowIso F K.obj).hom := sorry

/-- The inverse component of the common-domain comparison is the inverse canonical objectwise
bounded-below comparison. -/
@[simp, stacks 05T5 "inverse bounded-below source-defined-domain comparison component"]
theorem inv_app (F : A ⥤ B) [F.Additive] (K : Domain F) :
    (natIso F).inv.app K = (RightDerived.Value.boundedBelowIso F K.obj).inv := sorry

end natIso

namespace boundedFunctor

/-- The bounded-value functor evaluates to the included bounded pointwise value. -/
@[simp]
theorem obj (F : A ⥤ B) [F.Additive] (K : Domain F) :
    (boundedFunctor F).obj K = DerivedCategory.Plus.ι.obj
      (RightDerived.Value.obj F.toBoundedBelowDerived
        (HomotopyCategory.Plus.quasiIso A) K.obj) := sorry

/-- The bounded-value functor maps by the included bounded pointwise-value map. -/
@[simp]
theorem map (F : A ⥤ B) [F.Additive]
    {K L : Domain F} (f : K ⟶ L) :
    (boundedFunctor F).map f = DerivedCategory.Plus.ι.map
      (RightDerived.Value.map F.toBoundedBelowDerived
        (HomotopyCategory.Plus.quasiIso A) f.hom) := sorry

end boundedFunctor

namespace ambientFunctor

/-- The ambient-value functor evaluates to the ambient pointwise value. -/
@[simp]
theorem obj (F : A ⥤ B) [F.Additive] (K : Domain F) :
    (ambientFunctor F).obj K = RightDerived.Value.obj (Functor.Homotopy.toDerived F)
      (HomotopyCategory.quasiIso A (up ℤ)) K.obj.obj := sorry

/-- The ambient-value functor maps by the ambient pointwise-value map. -/
@[simp]
theorem map (F : A ⥤ B) [F.Additive]
    {K L : Domain F} (f : K ⟶ L) :
    (ambientFunctor F).map f = RightDerived.Value.map (Functor.Homotopy.toDerived F)
      (HomotopyCategory.quasiIso A (up ℤ)) f.hom.hom := sorry

end ambientFunctor

end CategoryTheory.Functor.RightDerived.Value.BoundedBelow
