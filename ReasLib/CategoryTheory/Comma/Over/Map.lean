/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Canonical maps involving identity objects in slice categories

This module contains elementary comparison data for `Over.map`. It is independent of
Grothendieck topologies, presheaves, and descent data. Besides the canonical isomorphisms, it
names the morphism from the image of an identity slice object to the next identity slice object;
the latter is the stable input used by evaluation and base-change constructions.
-/

@[expose] public section

universe u v

namespace CategoryTheory
namespace Over

variable {C : Type u} [Category.{v} C]

/-- The image of the identity object of `C/V` under `Over.map f` is canonically
isomorphic to the object represented by `f : V ⟶ U` in `C/U`. -/
noncomputable def mapIdentityIso {U V : C} (f : V ⟶ U) :
    (Over.map f).obj (Over.mk (𝟙 V)) ≅ Over.mk f :=
  Over.isoMk (Iso.refl V)

/-- The forward map of `mapIdentityIso f` is the identity on its underlying object. -/
@[simp]
theorem mapIdentityIso.hom.left {U V : C} (f : V ⟶ U) :
    (mapIdentityIso f).hom.left = 𝟙 V := rfl

/-- The inverse map of `mapIdentityIso f` is the identity on its underlying object. -/
@[simp]
theorem mapIdentityIso.inv.left {U V : C} (f : V ⟶ U) :
    (mapIdentityIso f).inv.left = 𝟙 V := rfl

/-- The canonical presentation of a slice object by its structure arrow. -/
noncomputable def mkHomIso {U : C} (Y : Over U) :
    Over.mk Y.hom ≅ Y :=
  Over.isoMk (Iso.refl Y.left) (Category.id_comp Y.hom)

/-- The forward map of `mkHomIso Y` is the identity on the underlying object of `Y`. -/
@[simp]
theorem mkHomIso.hom.left {U : C} (Y : Over U) :
    (mkHomIso Y).hom.left = 𝟙 Y.left := rfl

/-- The inverse map of `mkHomIso Y` is the identity on the underlying object of `Y`. -/
@[simp]
theorem mkHomIso.inv.left {U : C} (Y : Over U) :
    (mkHomIso Y).inv.left = 𝟙 Y.left := rfl

/-- The canonical arrow from the slice object represented by `f : V ⟶ U` to
the terminal identity object of `Over U`. -/
noncomputable def homMkTerminal {U V : C} (f : V ⟶ U) :
    Over.mk f ⟶ Over.mk (𝟙 U) :=
  mkIdTerminal.from (Over.mk f)

/-- The underlying arrow of `homMkTerminal f` is `f`. -/
@[simp]
theorem homMkTerminal.left {U V : C} (f : V ⟶ U) :
    (homMkTerminal f).left = f := by
  simp [homMkTerminal]

namespace mapIdentityToIdentity

/-- The underlying base arrow satisfies the triangle needed to map an identity slice object
along `Over.map f` and then to the identity slice object over the codomain. -/
theorem fac {U V : C} (f : U ⟶ V) :
    f ≫ (Over.mk (𝟙 V)).hom =
      ((Over.map f).obj (Over.mk (𝟙 U))).hom := by
  change f ≫ 𝟙 V = 𝟙 U ≫ f
  exact (Category.comp_id f).trans (Category.id_comp f).symm

end mapIdentityToIdentity

/-- The canonical morphism from the image of the identity slice object over `U` to the identity
slice object over `V`. Its underlying arrow is exactly `f : U ⟶ V`. -/
def mapIdentityToIdentity {U V : C} (f : U ⟶ V) :
    (Over.map f).obj (Over.mk (𝟙 U)) ⟶ Over.mk (𝟙 V) :=
  Over.homMk f (mapIdentityToIdentity.fac f)

/-- The underlying arrow of `mapIdentityToIdentity f` is `f`. -/
@[simp]
theorem mapIdentityToIdentity.left {U V : C} (f : U ⟶ V) :
    (mapIdentityToIdentity f).left = f := rfl

/-- For an identity base arrow, `mapIdentityToIdentity` is the component of the canonical
identity comparison for `Over.map`. -/
theorem mapIdentityToIdentity.id (U : C) :
    mapIdentityToIdentity (𝟙 U) =
      (Over.mapId U).hom.app (Over.mk (𝟙 U)) := by
  apply OverMorphism.ext
  rfl

/-- The canonical identity-object arrow is compatible with composition of base arrows and the
canonical composition comparison for `Over.map`. -/
theorem mapIdentityToIdentity.comp {U V W : C} (f : U ⟶ V) (g : V ⟶ W) :
    (Over.mapComp f g).hom.app (Over.mk (𝟙 U)) ≫
        (Over.map g).map (mapIdentityToIdentity f) ≫
          mapIdentityToIdentity g =
      mapIdentityToIdentity (f ≫ g) := by
  apply OverMorphism.ext
  change 𝟙 U ≫ f ≫ g = f ≫ g
  exact Category.id_comp (f ≫ g)

/- The non-`Prop` payload of these constructions is explicit, and the commuting-triangle
proof field of `mapIdentityToIdentity` is verified by `mapIdentityToIdentity.fac` above. -/

end Over
end CategoryTheory
