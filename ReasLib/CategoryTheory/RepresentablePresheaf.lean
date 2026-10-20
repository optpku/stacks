/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Yoneda

/-!
# Explicitly represented presheaves

The scoped notation `h[U]` denotes the Yoneda presheaf represented by `U`.  This file also
records the morphism between explicit representing objects induced by a natural transformation
and the universal-element equations for the canonical isomorphism between two representations.
-/

@[expose] public section

open CategoryTheory

universe w v u

namespace CategoryTheory

namespace RepresentablePresheaf

/- Scoped notation for the representable presheaf `h_U`. Since Lean does not support the
subscripted binder directly as notation, the reusable surface form is `h[U]`. -/
scoped notation:max "h[" U "]" => yoneda.obj U

/-- Evaluation at the identity gives an equivalence between natural transformations from a
representable presheaf and elements of the target presheaf, natural in both arguments. -/
def homEquiv {C : Type u} [Category.{v} C] {U : C} {F : Cᵒᵖ ⥤ Type v} :
    (yoneda.obj U ⟶ F) ≃ F.obj (Opposite.op U) :=
  CategoryTheory.yonedaEquiv

end RepresentablePresheaf

namespace Functor.RepresentableBy

variable {C : Type u} [Category.{v} C]
variable {F G H : Cᵒᵖ ⥤ Type w} {X X' Y Y' Z : C}

/-- The canonical isomorphism between two explicit representations carries the universal
element of the first representation to that of the second. -/
@[simp, stacks 001Q "canonical comparison of explicit representing objects"]
theorem uniqueUpToIso.hom_apply (R₁ : F.RepresentableBy X)
    (R₂ : F.RepresentableBy Y) :
    R₂.homEquiv (R₁.uniqueUpToIso R₂).hom = R₁.homEquiv (𝟙 X) := sorry

/-- The inverse canonical isomorphism between two explicit representations carries the
universal element of the second representation back to that of the first. -/
@[simp, stacks 001Q "canonical comparison of explicit representing objects"]
theorem uniqueUpToIso.inv_apply (R₁ : F.RepresentableBy X)
    (R₂ : F.RepresentableBy Y) :
    R₁.homEquiv (R₁.uniqueUpToIso R₂).inv = R₂.homEquiv (𝟙 Y) := sorry

/-- A natural transformation between explicitly represented presheaves induces a morphism
between their representing objects.  Keeping the representations explicit avoids installing
global `IsRepresentable` instances merely to obtain this map. -/
@[stacks 001Q "map between explicit representing objects"]
def map (RF : F.RepresentableBy X) (RG : G.RepresentableBy Y) (α : F ⟶ G) : X ⟶ Y :=
  RG.homEquiv.symm (α.app (Opposite.op X) (RF.homEquiv (𝟙 X)))

/-- The map between representing objects realizes the given natural transformation under the
two representing equivalences. -/
@[stacks 001Q "map between explicit representing objects"]
theorem homEquiv_map (RF : F.RepresentableBy X) (RG : G.RepresentableBy Y)
    (α : F ⟶ G) {A : C} (f : A ⟶ X) :
    RG.homEquiv (f ≫ RF.map RG α) = α.app (Opposite.op A) (RF.homEquiv f) := sorry

/-- Changing both explicit representations conjugates the map induced by a natural
transformation by the canonical comparison isomorphisms. -/
@[reassoc]
theorem map_naturality (RF : F.RepresentableBy X) (RF' : F.RepresentableBy X')
    (RG : G.RepresentableBy Y) (RG' : G.RepresentableBy Y') (α : F ⟶ G) :
    (RF.uniqueUpToIso RF').hom ≫ RF'.map RG' α =
      RF.map RG α ≫ (RG.uniqueUpToIso RG').hom := sorry

/-- The map induced by a natural transformation is contravariantly compatible with changing
only its source representation. -/
@[reassoc (attr := simp)]
theorem map_naturality_source (RF : F.RepresentableBy X) (RF' : F.RepresentableBy X')
    (RG : G.RepresentableBy Y) (α : F ⟶ G) :
    (RF.uniqueUpToIso RF').hom ≫ RF'.map RG α = RF.map RG α := sorry

/-- The map induced by a natural transformation is covariantly compatible with changing only
its target representation. -/
@[reassoc (attr := simp)]
theorem map_naturality_target (RF : F.RepresentableBy X) (RG : G.RepresentableBy Y)
    (RG' : G.RepresentableBy Y') (α : F ⟶ G) :
    RF.map RG α ≫ (RG.uniqueUpToIso RG').hom = RF.map RG' α := sorry

/-- The inverse canonical comparisons give the reverse orientation of change-of-representation
naturality for an induced map. -/
@[reassoc]
theorem map_naturality_inv (RF : F.RepresentableBy X) (RF' : F.RepresentableBy X')
    (RG : G.RepresentableBy Y) (RG' : G.RepresentableBy Y') (α : F ⟶ G) :
    (RF.uniqueUpToIso RF').inv ≫ RF.map RG α =
      RF'.map RG' α ≫ (RG.uniqueUpToIso RG').inv := sorry

/-- The identity natural transformation induces the identity of a representing object. -/
@[simp, stacks 001Q "identity map between explicit representing objects"]
theorem map_id (RF : F.RepresentableBy X) : RF.map RF (𝟙 F) = 𝟙 X := sorry

/-- Composition of natural transformations induces composition of the corresponding maps
between explicit representing objects. -/
@[simp, stacks 001Q "composition of maps between explicit representing objects"]
theorem map_comp (RF : F.RepresentableBy X) (RG : G.RepresentableBy Y)
    (RH : H.RepresentableBy Z) (α : F ⟶ G) (β : G ⟶ H) :
    RF.map RH (α ≫ β) = RF.map RG α ≫ RG.map RH β := sorry

end Functor.RepresentableBy

end CategoryTheory
