/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Limits.Presheaf

/-!
# Presheaf fiber (stalk) functor

For a set-valued functor `u : C ⥤ Type w`, the presheaf fiber functor sends a
presheaf `F : Cᵒᵖ ⥤ Type w` to the colimit of `F` over the opposite of the
category of elements of `u`. This is the general construction underlying stalks
at points of sites.

## Main definitions

- `Functor.presheafFiber` — the fiber/stalk functor `(Cᵒᵖ ⥤ Type w) ⥤ Type w`
- `Functor.toPresheafFiber` — generator map from sections to the fiber
- `Functor.presheafFiberDesc` — descent/universal property
-/

set_option backward.privateInPublic true

@[expose] public section

open CategoryTheory Limits Opposite CategoryOfElements

universe u v w

noncomputable section

namespace CategoryTheory.Functor

variable {C : Type u} [Category.{v} C]
variable (u : C ⥤ Type w)
variable [HasColimitsOfShape u.Elementsᵒᵖ (Type w)]

/-- The presheaf fiber functor: for each presheaf `F`, take the colimit of `F`
over the opposite category of elements of `u`. -/
abbrev presheafFiber : (Cᵒᵖ ⥤ Type w) ⥤ Type w :=
  (whiskeringLeft _ _ _).obj (π u).op ⋙ colim

/-- The canonical map from a section to the fiber, indexed by an element `x : u.obj X`. -/
abbrev toPresheafFiber (X : C) (x : u.obj X) (F : Cᵒᵖ ⥤ Type w) :
    F.obj (op X) ⟶ u.presheafFiber.obj F :=
  colimit.ι ((π u).op ⋙ F) (op (u.elementsMk X x))

/-- Two maps out of the fiber agree if they agree on all generators. -/
@[ext]
lemma presheafFiber_hom_ext {F : Cᵒᵖ ⥤ Type w} {E : Type w}
    {f g : u.presheafFiber.obj F ⟶ E}
    (h : ∀ (X : C) (x : u.obj X),
      u.toPresheafFiber X x F ≫ f = u.toPresheafFiber X x F ≫ g) :
    f = g := sorry

/-- Generators are compatible with presheaf restriction. -/
@[elementwise, simp, reassoc]
lemma toPresheafFiber_w
    {F : Cᵒᵖ ⥤ Type w} {X Y : C} (f : X ⟶ Y) (x : u.obj X) :
    F.map f.op ≫ u.toPresheafFiber X x F =
      u.toPresheafFiber Y (u.map f x) F := sorry

/-- Generators are natural in the presheaf argument. -/
@[elementwise, simp, reassoc]
lemma toPresheafFiber_naturality
    {F G : Cᵒᵖ ⥤ Type w} (f : F ⟶ G) (X : C) (x : u.obj X) :
    u.toPresheafFiber X x F ≫ u.presheafFiber.map f =
      f.app (op X) ≫ u.toPresheafFiber X x G := sorry

/-- A compatible family of maps defines a natural transformation to the constant diagram. -/
private theorem presheafFiberDesc_naturality {F : Cᵒᵖ ⥤ Type w} {E : Type w}
    (φ : ∀ (X : C) (_ : u.obj X), F.obj (op X) ⟶ E)
    (hφ : ∀ ⦃X Y : C⦄ (f : X ⟶ Y) (x : u.obj X),
      F.map f.op ≫ φ X x = φ Y (u.map f x))
    {j k : u.Elementsᵒᵖ} (arrow : j ⟶ k) :
    ((π u).op ⋙ F).map arrow ≫ φ k.unop.1 k.unop.2 =
      φ j.unop.1 j.unop.2 ≫ 𝟙 E := sorry

/-- Descend a compatible family of maps to a map out of the fiber. -/
noncomputable def presheafFiberDesc {F : Cᵒᵖ ⥤ Type w} {E : Type w}
    (φ : ∀ (X : C) (_ : u.obj X), F.obj (op X) ⟶ E)
    (hφ : ∀ ⦃X Y : C⦄ (f : X ⟶ Y) (x : u.obj X),
      F.map f.op ≫ φ X x = φ Y (u.map f x)) :
    u.presheafFiber.obj F ⟶ E :=
  colimit.desc ((π u).op ⋙ F) <|
    Cocone.mk E
      { app := fun j ↦ φ j.unop.1 j.unop.2
        naturality := fun _ _ arrow ↦ presheafFiberDesc_naturality u φ hφ arrow }

/-- Evaluating `presheafFiberDesc` on a canonical generator recovers the corresponding component
map. -/
@[simp, reassoc]
lemma toPresheafFiber_presheafFiberDesc {F : Cᵒᵖ ⥤ Type w} {E : Type w}
    (φ : ∀ (X : C) (_ : u.obj X), F.obj (op X) ⟶ E)
    (hφ : ∀ ⦃X Y : C⦄ (f : X ⟶ Y) (x : u.obj X),
      F.map f.op ≫ φ X x = φ Y (u.map f x))
    (X : C) (x : u.obj X) :
    u.toPresheafFiber X x F ≫ u.presheafFiberDesc φ hφ = φ X x := sorry

/-! ### Costalk (right adjoint to fiber) -/

variable (u : C ⥤ Type w)

/-- Precomposition by the image of an identity arrow acts identically on functions. -/
private theorem presheafCostalkObj_map_id (E : Type w) (X : Cᵒᵖ) :
    (TypeCat.ofHom fun (value : u.obj X.unop → E) element ↦
      value (u.map (𝟙 X).unop element)) = 𝟙 (u.obj X.unop → E) := sorry

/-- Precomposition by the image of a composite agrees with successive restrictions. -/
private theorem presheafCostalkObj_map_comp (E : Type w) {X Y Z : Cᵒᵖ}
    (first : X ⟶ Y) (second : Y ⟶ Z) :
    (TypeCat.ofHom fun (value : u.obj X.unop → E) element ↦
      value (u.map (first ≫ second).unop element)) =
      (TypeCat.ofHom fun (value : u.obj X.unop → E) element ↦
        value (u.map first.unop element)) ≫
      (TypeCat.ofHom fun (value : u.obj Y.unop → E) element ↦
        value (u.map second.unop element)) := sorry

/-- The presheaf of functions from the values of `u` to a fixed set. -/
private def presheafCostalkObj (E : Type w) : Cᵒᵖ ⥤ Type w where
  obj X := u.obj X.unop → E
  map arrow := TypeCat.ofHom fun value element ↦ value (u.map arrow.unop element)
  map_id := presheafCostalkObj_map_id u E
  map_comp := presheafCostalkObj_map_comp u E

/-- Postcomposition of functions commutes with restriction by precomposition. -/
private theorem presheafCostalkMap_naturality {E E' : Type w} (map : E ⟶ E')
    {X Y : Cᵒᵖ} (arrow : X ⟶ Y) :
    (TypeCat.ofHom fun (value : u.obj X.unop → E) element ↦
      value (u.map arrow.unop element)) ≫
      (TypeCat.ofHom fun (value : u.obj Y.unop → E) element ↦ map (value element)) =
      (TypeCat.ofHom fun (value : u.obj X.unop → E) element ↦ map (value element)) ≫
      (TypeCat.ofHom fun (value : u.obj X.unop → E') element ↦
        value (u.map arrow.unop element)) := sorry

/-- Postcomposition induces a natural transformation between function-valued presheaves. -/
private def presheafCostalkMap {E E' : Type w} (map : E ⟶ E') :
    presheafCostalkObj u E ⟶ presheafCostalkObj u E' where
  app _ := TypeCat.ofHom fun value element ↦ map (value element)
  naturality _ _ arrow := presheafCostalkMap_naturality u map arrow

/-- Postcomposition with an identity induces the identity natural transformation. -/
private theorem presheafCostalk_map_id (E : Type w) :
    presheafCostalkMap u (𝟙 E) = 𝟙 (presheafCostalkObj u E) := sorry

/-- Postcomposition preserves composition as a natural transformation of presheaves. -/
private theorem presheafCostalk_map_comp {E E' E'' : Type w}
    (first : E ⟶ E') (second : E' ⟶ E'') :
    presheafCostalkMap u (first ≫ second) =
      presheafCostalkMap u first ≫ presheafCostalkMap u second := sorry

/-- The presheaf-valued costalk functor: sends a set `E` to the presheaf `X ↦ (u.obj X → E)`.
This is right adjoint to `presheafFiber u`. -/
abbrev presheafCostalk : Type w ⥤ Cᵒᵖ ⥤ Type w where
  obj := presheafCostalkObj u
  map := presheafCostalkMap u
  map_id := presheafCostalk_map_id u
  map_comp := presheafCostalk_map_comp u

section

variable [HasColimitsOfShape u.Elementsᵒᵖ (Type w)]

/-- Evaluation of a fiber map on generators is natural under presheaf restriction. -/
private theorem presheafFiberCostalkTo_naturality {F : Cᵒᵖ ⥤ Type w} {E : Type w}
    (φ : u.presheafFiber.obj F ⟶ E) {X Y : Cᵒᵖ} (arrow : X ⟶ Y) :
    F.map arrow ≫ (TypeCat.ofHom fun (value : F.obj Y) element ↦
      φ (colimit.ι ((π u).op ⋙ F) (op (u.elementsMk Y.unop element)) value)) =
      (TypeCat.ofHom fun (value : F.obj X) element ↦
        φ (colimit.ι ((π u).op ⋙ F) (op (u.elementsMk X.unop element)) value)) ≫
      (u.presheafCostalk.obj E).map arrow := sorry

/-- A map from a presheaf fiber induces a costalk transformation by evaluating generators. -/
private def presheafFiberCostalkTo {F : Cᵒᵖ ⥤ Type w} {E : Type w}
    (φ : u.presheafFiber.obj F ⟶ E) : F ⟶ u.presheafCostalk.obj E where
  app X := TypeCat.ofHom fun value element ↦
    φ (colimit.ι ((π u).op ⋙ F) (op (u.elementsMk X.unop element)) value)
  naturality _ _ arrow := presheafFiberCostalkTo_naturality u φ arrow

/-- Evaluation of a costalk transformation is natural on the opposite category of elements. -/
private theorem presheafFiberCostalkFrom_naturality {F : Cᵒᵖ ⥤ Type w} {E : Type w}
    (ψ : F ⟶ u.presheafCostalk.obj E) {j k : u.Elementsᵒᵖ} (arrow : j ⟶ k) :
    ((π u).op ⋙ F).map arrow ≫
      (TypeCat.ofHom fun (value : F.obj (op k.unop.1)) ↦
        ψ.app (op k.unop.1) value k.unop.2) =
      (TypeCat.ofHom fun (value : F.obj (op j.unop.1)) ↦
        ψ.app (op j.unop.1) value j.unop.2) ≫ 𝟙 E := sorry

/-- A costalk transformation induces a map from the fiber by colimit descent. -/
private def presheafFiberCostalkFrom {F : Cᵒᵖ ⥤ Type w} {E : Type w}
    (ψ : F ⟶ u.presheafCostalk.obj E) : u.presheafFiber.obj F ⟶ E :=
  colimit.desc ((π u).op ⋙ F)
    { pt := E
      ι := { app := fun j ↦ TypeCat.ofHom fun value ↦
               ψ.app (op j.unop.1) value j.unop.2
             naturality := fun _ _ arrow ↦ presheafFiberCostalkFrom_naturality u ψ arrow } }

/-- Descent after evaluation on generators recovers the original map from the fiber. -/
private theorem presheafFiberCostalk_left_inv {F : Cᵒᵖ ⥤ Type w} {E : Type w}
    (φ : u.presheafFiber.obj F ⟶ E) :
    presheafFiberCostalkFrom u (presheafFiberCostalkTo u φ) = φ := sorry

/-- Evaluation on generators after descent recovers the original costalk transformation. -/
private theorem presheafFiberCostalk_right_inv {F : Cᵒᵖ ⥤ Type w} {E : Type w}
    (ψ : F ⟶ u.presheafCostalk.obj E) :
    presheafFiberCostalkTo u (presheafFiberCostalkFrom u ψ) = ψ := sorry

/-- Descent of costalk transformations commutes with precomposition in the presheaf. -/
private theorem presheafFiberCostalk_naturality_left_symm
    {F' F : Cᵒᵖ ⥤ Type w} {E : Type w}
    (map : F' ⟶ F) (ψ : F ⟶ u.presheafCostalk.obj E) :
    presheafFiberCostalkFrom u (map ≫ ψ) =
      u.presheafFiber.map map ≫ presheafFiberCostalkFrom u ψ := sorry

/-- Evaluation on generators commutes with postcomposition of maps from the fiber. -/
private theorem presheafFiberCostalk_naturality_right
    {F : Cᵒᵖ ⥤ Type w} {E E' : Type w}
    (φ : u.presheafFiber.obj F ⟶ E) (map : E ⟶ E') :
    presheafFiberCostalkTo u (φ ≫ map) =
      presheafFiberCostalkTo u φ ≫ u.presheafCostalk.map map := sorry

end

/-- The fiber-costalk adjunction: `presheafFiber u ⊣ presheafCostalk u`. -/
noncomputable def presheafFiberCostalkAdj
    [HasColimitsOfShape u.Elementsᵒᵖ (Type w)] :
    u.presheafFiber ⊣ u.presheafCostalk :=
  Adjunction.mkOfHomEquiv {
    homEquiv := fun _ _ ↦ {
      toFun := presheafFiberCostalkTo u
      invFun := presheafFiberCostalkFrom u
      left_inv := presheafFiberCostalk_left_inv u
      right_inv := presheafFiberCostalk_right_inv u }
    homEquiv_naturality_left_symm := presheafFiberCostalk_naturality_left_symm u
    homEquiv_naturality_right := presheafFiberCostalk_naturality_right u }

/-- The presheaf-valued costalk of `u` is right adjoint to its presheaf fiber functor. -/
instance presheafCostalk_isRightAdjoint
    [HasColimitsOfShape u.Elementsᵒᵖ (Type w)] : u.presheafCostalk.IsRightAdjoint := sorry

end CategoryTheory.Functor
