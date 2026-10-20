/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.CompleteLocalAlgebra.Hom
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Basic
public import Mathlib.CategoryTheory.FiberedCategory.Fiber

/-! # Complete local objects and local morphisms

Objects lie over spectra of Noetherian complete local algebras with finite-type
residue field. Morphisms are arrows inducing local homomorphisms of these algebras.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor IsLocalRing

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} [IsLocallyNoetherian S]

/-- An object over a Noetherian complete local algebra with finite-type residue field. -/
def CompleteLocalObject (X : GroupoidsOver S) :=
  Σ' base : CompleteLocalSAlgebra S,
    Σ' object : X.total, X.p.obj object = Over.mk base.toS

namespace CompleteLocalObject

variable {X : GroupoidsOver S}

/-- The complete local algebra underlying an object. -/
def base (x : CompleteLocalObject X) : CompleteLocalSAlgebra S := x.1

/-- The underlying object of the total category. -/
def object (x : CompleteLocalObject X) : X.total := x.2.1

/-- The underlying object lies over its complete local spectrum. -/
def over_obj (x : CompleteLocalObject X) :
    X.p.obj x.object = Over.mk x.base.toS := x.2.2

/-- Package an object over a complete local spectrum. -/
def of (base : CompleteLocalSAlgebra S) (object : X.total)
    (over_obj : X.p.obj object = Over.mk base.toS) : CompleteLocalObject X :=
  ⟨base, object, over_obj⟩

/-- A complete local object lies over its stored spectrum. -/
theorem spec (x : CompleteLocalObject X) :
    X.p.obj x.object = Over.mk x.base.toS := x.over_obj

/-- Underlying morphism of spectra induced by a morphism of complete local
objects. -/
def schemeHom {x y : CompleteLocalObject X} (f : x.object ⟶ y.object) :
    Spec (CommRingCat.of x.base.carrier) ⟶ Spec (CommRingCat.of y.base.carrier) :=
  eqToHom (congrArg Over.left x.over_obj).symm ≫ (X.p.map f).left ≫
    eqToHom (congrArg Over.left y.over_obj)

/-- Ring homomorphism associated to a morphism of complete local objects. -/
def ringHom {x y : CompleteLocalObject X} (f : x.object ⟶ y.object) :
    y.base.carrier →+* x.base.carrier :=
  CommRingCat.Hom.hom <|
    (Scheme.ΓSpecIso (CommRingCat.of y.base.carrier)).inv ≫ (schemeHom f).appTop ≫
      (Scheme.ΓSpecIso (CommRingCat.of x.base.carrier)).hom

/-- Morphisms of complete local objects are arrows whose induced ring maps are local. -/
def Hom (x y : CompleteLocalObject X) :=
  {f : x.object ⟶ y.object // IsLocalHom (ringHom f)}

/-- Package an arrow with its locality condition. -/
def Hom.of {x y : CompleteLocalObject X} (f : x.object ⟶ y.object)
    (hf : IsLocalHom (ringHom f)) : Hom x y := ⟨f, hf⟩

/-- The underlying arrow of a local morphism. -/
def Hom.hom {x y : CompleteLocalObject X} (f : Hom x y) : x.object ⟶ y.object := f.1

/-- The ring map of a local morphism is local. -/
theorem ringHom_isLocalHom {x y : CompleteLocalObject X} (f : Hom x y) :
    IsLocalHom (ringHom f.hom) := f.2

/-- The spectrum of the induced ring map lies over `S`. -/
theorem ringHom_over_S {x y : CompleteLocalObject X} (f : x.object ⟶ y.object) :
    Spec.map (CommRingCat.ofHom (ringHom f)) ≫ y.base.toS = x.base.toS :=
  sorry

/-- Extracting the identity arrow gives the identity ring map. -/
theorem ringHom_id (x : CompleteLocalObject X) :
    ringHom (𝟙 x.object) = RingHom.id x.base.carrier := sorry

/-- Extracting a composite gives the contravariant composite of ring maps. -/
theorem ringHom_comp {x y z : CompleteLocalObject X}
    (f : x.object ⟶ y.object) (g : y.object ⟶ z.object) :
    ringHom (f ≫ g) = (ringHom f).comp (ringHom g) := sorry

/-- The local base morphism extracted from a local morphism of objects. -/
def baseHom {x y : CompleteLocalObject X} (f : Hom x y) :
    CompleteLocalSAlgebra.Hom x.base y.base where
  hom := ringHom f.hom
  isLocalHom := ringHom_isLocalHom f
  over_S := ringHom_over_S f.hom

/-- The underlying ring map of the extracted base morphism is the induced ring map. -/
theorem baseHom_hom {x y : CompleteLocalObject X} (f : Hom x y) :
    (baseHom f).hom = ringHom f.hom := rfl

/-- Underlying morphism in `Over S` induced by a morphism of complete local
objects. -/
def overHom {x y : CompleteLocalObject X} (f : x.object ⟶ y.object) :
    Over.mk x.base.toS ⟶ Over.mk y.base.toS :=
  eqToHom x.over_obj.symm ≫ X.p.map f ≫ eqToHom y.over_obj

/-- A morphism of complete local objects lies over `overHom`. -/
theorem overHom_isHomLift {x y : CompleteLocalObject X} (f : x.object ⟶ y.object) :
    X.p.IsHomLift (overHom f) f :=
  IsHomLift.of_fac X.p (overHom f) f x.over_obj y.over_obj rfl

/-- The identity local morphism. -/
def Hom.id (x : CompleteLocalObject X) : Hom x x :=
  ⟨𝟙 x.object, by rw [ringHom_id]; exact isLocalHom_id x.base.carrier⟩

/-- Composition of local morphisms, with locality preserved by composition. -/
def Hom.comp {x y z : CompleteLocalObject X} (f : Hom x y) (g : Hom y z) : Hom x z :=
  ⟨f.hom ≫ g.hom, by
    rw [ringHom_comp]
    exact @RingHom.isLocalHom_comp _ _ _ _ _ _ (ringHom f.hom) (ringHom g.hom)
      f.2 g.2⟩

/-- The category of complete local objects and arrows inducing local ring maps. -/
instance category : Category.{u} (CompleteLocalObject X) where
  toQuiver := ⟨fun x y ↦ {f : x.object ⟶ y.object // IsLocalHom (ringHom f)}⟩
  id x := ⟨𝟙 x.object, by rw [ringHom_id]; exact isLocalHom_id x.base.carrier⟩
  comp f g := ⟨f.1 ≫ g.1, by
    rw [ringHom_comp]
    exact @RingHom.isLocalHom_comp _ _ _ _ _ _ (ringHom f.1) (ringHom g.1)
      f.2 g.2⟩
  id_comp f := Subtype.ext (Category.id_comp f.1)
  comp_id f := Subtype.ext (Category.comp_id f.1)
  assoc f g h := Subtype.ext (Category.assoc f.1 g.1 h.1)

/-- Forget the locality condition on arrows and the complete local presentation. -/
def forget : CompleteLocalObject X ⥤ X.total where
  obj x := x.object
  map f := Hom.hom f
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The forgetful functor returns the underlying object. -/
theorem forget_obj (x : CompleteLocalObject X) : forget.obj x = x.object := rfl

/-- A fibre object over a complete local spectrum determines a complete local object. -/
def ofFiber (R : CompleteLocalSAlgebra S) (x : X.p.Fiber (Over.mk R.toS)) :
    CompleteLocalObject X := of R (Fiber.fiberInclusion.obj x) x.property

/-- A fibre arrow over a fixed complete local spectrum induces the identity ring map. -/
theorem ringHom_fiberInclusion (R : CompleteLocalSAlgebra S)
    {x y : X.p.Fiber (Over.mk R.toS)} (f : x ⟶ y) :
    ringHom (x := ofFiber R x) (y := ofFiber R y) (Fiber.fiberInclusion.map f) =
      RingHom.id R.carrier := sorry

/-- A fibre arrow over a complete local spectrum determines a local morphism. -/
def Hom.ofFiber (R : CompleteLocalSAlgebra S)
    {x y : X.p.Fiber (Over.mk R.toS)} (f : x ⟶ y) : Hom (ofFiber R x) (ofFiber R y) :=
  Hom.of (Fiber.fiberInclusion.map f) (by
    rw [ringHom_fiberInclusion R f]
    exact isLocalHom_id R.carrier)

end CompleteLocalObject

end AlgebraicGeometry.GroupoidsOver
