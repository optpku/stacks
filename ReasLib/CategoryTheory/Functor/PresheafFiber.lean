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

/-- Two maps out of the fiber agree iff they agree on all generators. -/
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

/-- Descend a compatible family of maps to a map out of the fiber. -/
noncomputable def presheafFiberDesc {F : Cᵒᵖ ⥤ Type w} {E : Type w}
    (φ : ∀ (X : C) (_ : u.obj X), F.obj (op X) ⟶ E)
    (hφ : ∀ ⦃X Y : C⦄ (f : X ⟶ Y) (x : u.obj X),
      F.map f.op ≫ φ X x = φ Y (u.map f x) := sorry) :
    u.presheafFiber.obj F ⟶ E :=
  colimit.desc ((π u).op ⋙ F) <|
    Cocone.mk E
      { app := fun j ↦ φ j.unop.1 j.unop.2
        naturality := sorry }

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

/-- The presheaf-valued costalk functor: sends a set `E` to the presheaf `X ↦ (u.obj X → E)`.
This is right adjoint to `presheafFiber u`. -/
abbrev presheafCostalk : Type w ⥤ Cᵒᵖ ⥤ Type w where
  obj E :=
    { obj := fun X ↦ u.obj X.unop → E
      map := fun {X Y} (f : X ⟶ Y) ↦ TypeCat.ofHom fun h x ↦ h (u.map f.unop x)
      map_id := sorry
      map_comp := sorry }
  map g :=
    { app := fun _ ↦ TypeCat.ofHom fun h x ↦ g (h x)
      naturality := sorry }
  map_id := sorry
  map_comp := sorry

/-- The fiber-costalk adjunction: `presheafFiber u ⊣ presheafCostalk u`. -/
noncomputable def presheafFiberCostalkAdj
    [HasColimitsOfShape u.Elementsᵒᵖ (Type w)] :
    u.presheafFiber ⊣ u.presheafCostalk :=
  Adjunction.mkOfHomEquiv {
    homEquiv := fun F E ↦ {
      toFun := fun φ ↦
        { app := fun X ↦ TypeCat.ofHom fun s x ↦
            φ (colimit.ι ((π u).op ⋙ F) (op (u.elementsMk X.unop x)) s)
          naturality := sorry }
      invFun := fun ψ ↦
        colimit.desc ((π u).op ⋙ F)
          { pt := E
            ι := { app := fun j ↦ TypeCat.ofHom fun s ↦ ψ.app (op j.unop.1) s j.unop.2
                   naturality := sorry } }
      left_inv := sorry
      right_inv := sorry }
    homEquiv_naturality_left_symm := sorry
    homEquiv_naturality_right := sorry }

/-- The presheaf-valued costalk of `u` is right adjoint to its presheaf fiber functor. -/
instance presheafCostalk_isRightAdjoint
    [HasColimitsOfShape u.Elementsᵒᵖ (Type w)] : u.presheafCostalk.IsRightAdjoint := sorry

end CategoryTheory.Functor
