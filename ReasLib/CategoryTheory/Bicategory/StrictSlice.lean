/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.StrictCostructuredArrow

/-!
# Strict slices of a strict bicategory

`StrictSlice X` is the identity-pseudofunctor specialization of the generic
strict costructured-arrow construction.  This module supplies the conventional
slice-object, map, and cell interfaces; generic infrastructure is owned by
`StrictCostructuredArrow`.
-/

@[expose] public section

universe wC vC uC

namespace CategoryTheory

open Bicategory
open scoped Bicategory

namespace Bicategory

variable {C : Type uC} [Bicategory.{wC, vC} C]

/-- The strict slice bicategory over `X`. -/
def StrictSlice [Bicategory.Strict C] (X : C) :=
  StrictCostructuredArrow (StrictPseudofunctor.id C) X

namespace StrictSlice

variable [Bicategory.Strict C] {X : C}

/-- Construct an object of a strict slice from its domain and structural arrow. -/
def mk (obj : C) (hom : obj ⟶ X) : StrictSlice X :=
  ⟨obj, hom⟩

/-- The domain object of an object of a strict slice. -/
abbrev obj (S : StrictSlice X) : C :=
  S.left

/-- The structural arrow of an object of a strict slice. -/
abbrev hom (S : StrictSlice X) : S.obj ⟶ X :=
  StrictCostructuredArrow.hom S

/-- The domain of a constructed strict-slice object is the supplied domain. -/
@[simp]
theorem mk_obj (obj : C) (hom : obj ⟶ X) :
    (mk obj hom).obj = obj := sorry

/-- The structural arrow of a constructed strict-slice object is the supplied arrow. -/
@[simp]
theorem mk_hom (obj : C) (hom : obj ⟶ X) :
    (mk obj hom).hom = hom := sorry

/-- Strict-slice objects are determined by their domain and structural arrow. -/
@[ext]
theorem ext {S T : StrictSlice X} (hobj : S.obj = T.obj)
    (hhom : HEq S.hom T.hom) :
    S = T := sorry

/-- The bicategory structure on a strict slice. -/
instance bicategory : Bicategory (StrictSlice X) :=
  inferInstanceAs
    (Bicategory
      (StrictCostructuredArrow (StrictPseudofunctor.id C) X))

/-- A strict slice is a strict bicategory. -/
instance strict : Bicategory.Strict (StrictSlice X) :=
  inferInstanceAs
    (Bicategory.Strict
      (StrictCostructuredArrow (StrictPseudofunctor.id C) X))

namespace Hom

/-- The ambient `1`-morphism underlying a strict-slice morphism. -/
abbrev hom {S T : StrictSlice X} (f : S ⟶ T) :
    S.obj ⟶ T.obj :=
  StrictCostructuredArrow.map f

/-- The ambient map of a strict-slice morphism commutes with the structural arrows. -/
theorem comm {S T : StrictSlice X} (f : S ⟶ T) :
    Hom.hom f ≫ StrictSlice.hom T = StrictSlice.hom S := sorry

namespace Implementation

/-- The identity strict pseudofunctor turns a commuting strict-slice triangle into the generic
strict costructured-arrow comparison equation. -/
theorem homMk_comm {S T : StrictSlice X} (hom : S.obj ⟶ T.obj)
    (comm : hom ≫ StrictSlice.hom T = StrictSlice.hom S) :
    (StrictPseudofunctor.id C).map hom ≫ StrictSlice.hom T =
      StrictSlice.hom S := sorry

end Implementation

/-- Construct a strict-slice morphism from a commuting triangle. -/
def mk {S T : StrictSlice X} (hom : S.obj ⟶ T.obj)
    (comm : hom ≫ StrictSlice.hom T = StrictSlice.hom S) :
    S ⟶ T :=
  StrictCostructuredArrow.homMk hom (Implementation.homMk_comm hom comm)

/-- The ambient map of a constructed strict-slice morphism is the supplied map. -/
@[simp]
theorem mk_hom {S T : StrictSlice X} (hom : S.obj ⟶ T.obj)
    (comm : hom ≫ StrictSlice.hom T = StrictSlice.hom S) :
    Hom.hom (mk hom comm) = hom := sorry

/-- The ambient map of a strict-slice identity is an identity. -/
@[simp]
theorem id_hom (S : StrictSlice X) :
    Hom.hom (𝟙 S) = 𝟙 S.obj := sorry

/-- The ambient map of a composite strict-slice morphism is the composite ambient map. -/
@[simp]
theorem comp_hom {R S T : StrictSlice X} (f : R ⟶ S) (g : S ⟶ T) :
    Hom.hom (f ≫ g) = Hom.hom f ≫ Hom.hom g := sorry

/-- Strict-slice morphisms are determined by their ambient maps. -/
@[ext]
theorem ext {S T : StrictSlice X} {f g : S ⟶ T}
    (h : Hom.hom f = Hom.hom g) :
    f = g := sorry

end Hom

namespace Hom₂

/-- The ambient `2`-morphism underlying a strict-slice `2`-morphism. -/
abbrev hom {S T : StrictSlice X} {f g : S ⟶ T} (η : f ⟶ g) :
    Hom.hom f ⟶ Hom.hom g :=
  StrictCostructuredArrow.map₂ η

/-- The ambient cell of a strict-slice `2`-morphism is compatible with the two commuting
triangles. -/
theorem comm {S T : StrictSlice X} {f g : S ⟶ T} (η : f ⟶ g) :
    Hom₂.hom η ▷ StrictSlice.hom T ≫ eqToHom (Hom.comm g) =
      eqToHom (Hom.comm f) := sorry

namespace Implementation

/-- Compatibility for a strict-slice `2`-cell implies the generic compatibility equation for
the identity strict pseudofunctor. -/
theorem hom₂Mk_comm {S T : StrictSlice X} {f g : S ⟶ T}
    (hom : Hom.hom f ⟶ Hom.hom g)
    (comm : hom ▷ StrictSlice.hom T ≫ eqToHom (Hom.comm g) =
      eqToHom (Hom.comm f)) :
    (StrictPseudofunctor.id C).map₂ hom ▷ StrictSlice.hom T ≫
        eqToHom (StrictCostructuredArrow.comm g) =
      eqToHom (StrictCostructuredArrow.comm f) := sorry

end Implementation

/-- Construct a strict-slice `2`-morphism from a compatible ambient cell. -/
def mk {S T : StrictSlice X} {f g : S ⟶ T}
    (hom : Hom.hom f ⟶ Hom.hom g)
    (comm : hom ▷ StrictSlice.hom T ≫ eqToHom (Hom.comm g) =
      eqToHom (Hom.comm f)) :
    f ⟶ g :=
  StrictCostructuredArrow.hom₂Mk hom (Implementation.hom₂Mk_comm hom comm)

/-- The ambient cell of a constructed strict-slice `2`-morphism is the supplied cell. -/
@[simp]
theorem mk_hom {S T : StrictSlice X} {f g : S ⟶ T}
    (hom : Hom.hom f ⟶ Hom.hom g)
    (comm : hom ▷ StrictSlice.hom T ≫ eqToHom (Hom.comm g) =
      eqToHom (Hom.comm f)) :
    Hom₂.hom (mk hom comm) = hom := sorry

/-- The ambient cell of a strict-slice identity `2`-morphism is an identity cell. -/
@[simp]
theorem id_hom {S T : StrictSlice X} (f : S ⟶ T) :
    Hom₂.hom (𝟙 f) = 𝟙 (Hom.hom f) := sorry

/-- The ambient cell of a vertically composite strict-slice `2`-morphism is the vertical
composite of the ambient cells. -/
@[simp]
theorem comp_hom {S T : StrictSlice X} {f g h : S ⟶ T}
    (η : f ⟶ g) (θ : g ⟶ h) :
    Hom₂.hom (η ≫ θ) = Hom₂.hom η ≫ Hom₂.hom θ := sorry

/-- The ambient cell of a left-whiskered strict-slice `2`-morphism is the corresponding
left whiskering of ambient data. -/
@[simp]
theorem whiskerLeft_hom {S T U : StrictSlice X}
    (f : S ⟶ T) {g h : T ⟶ U} (η : g ⟶ h) :
    Hom₂.hom (f ◁ η) = Hom.hom f ◁ Hom₂.hom η := sorry

/-- The ambient cell of a right-whiskered strict-slice `2`-morphism is the corresponding
right whiskering of ambient data. -/
@[simp]
theorem whiskerRight_hom {S T U : StrictSlice X}
    {f g : S ⟶ T} (η : f ⟶ g) (h : T ⟶ U) :
    Hom₂.hom (η ▷ h) = Hom₂.hom η ▷ Hom.hom h := sorry

/-- Strict-slice `2`-morphisms are determined by their ambient cells. -/
@[ext]
theorem ext {S T : StrictSlice X} {f g : S ⟶ T} {η θ : f ⟶ g}
    (h : Hom₂.hom η = Hom₂.hom θ) :
    η = θ := sorry

end Hom₂

end StrictSlice

end Bicategory

end CategoryTheory
