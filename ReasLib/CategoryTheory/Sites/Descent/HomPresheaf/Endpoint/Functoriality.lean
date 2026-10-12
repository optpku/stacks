/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Descent.HomPresheaf.Endpoint.Actions
public import ReasLib.CategoryTheory.Sites.Descent.HomPresheaf.Endpoint.Conjugation

/-!
# Endpoint functoriality for canonical Hom-presheaves

The separate contravariant and covariant endpoint actions assemble into a
presheaf-valued Hom functor. This module also records the identity,
composition, interchange, and endpoint-isomorphism formulas needed by later
strong-transformation constructions.
-/

@[expose] public section

universe uC vC uP vP

namespace CategoryTheory

open Opposite
open scoped CategoryTheory.Bicategory

namespace Pseudofunctor

variable {C : Type uC} [Category.{vC} C]

/-- Postcomposition by an identity morphism is the identity transformation. -/
@[simp]
theorem PresheafHom.Postcomp.id
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{vP, uP})
    {U : C} (x y : F.obj (.mk (op U))) :
    PresheafHom.Postcomp.map F (x := x) (𝟙 y) =
      𝟙 (F.presheafHom x y) := sorry

/-- Postcomposition by a composite is the composite of the two postcomposition
transformations. -/
theorem PresheafHom.Postcomp.comp
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{vP, uP})
    {U : C} (w : F.obj (.mk (op U))) {x y z : F.obj (.mk (op U))}
    (φ : x ⟶ y) (ψ : y ⟶ z) :
    PresheafHom.Postcomp.map F (x := w) (φ ≫ ψ) =
      PresheafHom.Postcomp.map F (x := w) φ ≫
        PresheafHom.Postcomp.map F (x := w) ψ := sorry

/-- Precomposition by an identity morphism is the identity transformation. -/
@[simp]
theorem PresheafHom.Precomp.id
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{vP, uP})
    {U : C} (x z : F.obj (.mk (op U))) :
    PresheafHom.Precomp.map F (z := z) (𝟙 x) =
      𝟙 (F.presheafHom x z) := sorry

/-- Precomposition reverses the order of composition. -/
theorem PresheafHom.Precomp.comp
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{vP, uP})
    {U : C} {w x y : F.obj (.mk (op U))}
    (z : F.obj (.mk (op U))) (φ : w ⟶ x) (ψ : x ⟶ y) :
    PresheafHom.Precomp.map F (z := z) (φ ≫ ψ) =
      PresheafHom.Precomp.map F (z := z) ψ ≫
        PresheafHom.Precomp.map F (z := z) φ := sorry

/-- Precomposition and postcomposition commute on canonical Hom-presheaves. -/
theorem PresheafHom.Precomp.postcomp
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{vP, uP})
    {U : C} {w x y z : F.obj (.mk (op U))}
    (φ : w ⟶ x) (ψ : y ⟶ z) :
    PresheafHom.Postcomp.map F (x := x) ψ ≫
        PresheafHom.Precomp.map F (z := z) φ =
      PresheafHom.Precomp.map F (z := y) φ ≫
        PresheafHom.Postcomp.map F (x := w) ψ := sorry

/-- Simultaneous contravariant/covariant action of morphisms in the two endpoints of a
canonical Hom-presheaf. -/
def PresheafHom.Endpoints.map
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{vP, uP})
    {U : C} {x₁ x₂ y₁ y₂ : F.obj (.mk (op U))}
    (φ : x₂ ⟶ x₁) (ψ : y₁ ⟶ y₂) :
    F.presheafHom x₁ y₁ ⟶ F.presheafHom x₂ y₂ :=
  PresheafHom.Precomp.map F (z := y₁) φ ≫
    PresheafHom.Postcomp.map F (x := x₂) ψ

/-- Elementwise computation of the simultaneous endpoint action. -/
@[simp]
theorem PresheafHom.Endpoints.Map.appApply
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{vP, uP})
    {U : C} {x₁ x₂ y₁ y₂ : F.obj (.mk (op U))}
    (φ : x₂ ⟶ x₁) (ψ : y₁ ⟶ y₂)
    (W : (Over U)ᵒᵖ) (δ : (F.presheafHom x₁ y₁).obj W) :
    (PresheafHom.Endpoints.map F φ ψ).app W δ =
      (F.map W.unop.hom.op.toLoc).toFunctor.map φ ≫ δ ≫
        (F.map W.unop.hom.op.toLoc).toFunctor.map ψ := sorry

/-- At the identity slice, simultaneous endpoint action is ordinary pre- and
postcomposition. -/
@[simp]
theorem PresheafHom.Endpoints.Map.identitySlice
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{vP, uP})
    {U : C} {x₁ x₂ y₁ y₂ : F.obj (.mk (op U))}
    (φ : x₂ ⟶ x₁) (ψ : y₁ ⟶ y₂) (δ : x₁ ⟶ y₁) :
    (PresheafHom.Endpoints.map F φ ψ).app (op (Over.mk (𝟙 U)))
        (F.presheafHomObjHomEquiv δ) =
      F.presheafHomObjHomEquiv (φ ≫ δ ≫ ψ) := sorry

/-- Simultaneous action by identity endpoint morphisms is the identity transformation. -/
@[simp]
theorem PresheafHom.Endpoints.Map.id
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{vP, uP})
    {U : C} (x y : F.obj (.mk (op U))) :
    PresheafHom.Endpoints.map F (𝟙 x) (𝟙 y) =
      𝟙 (F.presheafHom x y) := sorry

/-- Simultaneous endpoint actions compose contravariantly in the source endpoint and
covariantly in the target endpoint. -/
theorem PresheafHom.Endpoints.Map.comp
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{vP, uP})
    {U : C}
    {x₁ x₂ x₃ y₁ y₂ y₃ : F.obj (.mk (op U))}
    (φ₁ : x₂ ⟶ x₁) (φ₂ : x₃ ⟶ x₂)
    (ψ₁ : y₁ ⟶ y₂) (ψ₂ : y₂ ⟶ y₃) :
    PresheafHom.Endpoints.map F (φ₂ ≫ φ₁) (ψ₁ ≫ ψ₂) =
      PresheafHom.Endpoints.map F φ₁ ψ₁ ≫
        PresheafHom.Endpoints.map F φ₂ ψ₂ := sorry

/-- The canonical Hom-presheaf, functorial contravariantly in its source endpoint and
covariantly in its target endpoint. This is the presheaf-valued analogue of
`CategoryTheory.Functor.hom`. -/
def PresheafHom.Endpoints.functor
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{vP, uP}) (U : C) :
    (F.obj (.mk (op U)))ᵒᵖ × F.obj (.mk (op U)) ⥤
      ((Over U)ᵒᵖ ⥤ Type vP) where
  obj p := F.presheafHom p.1.unop p.2
  map f := PresheafHom.Endpoints.map F f.1.unop f.2
  map_id p := PresheafHom.Endpoints.Map.id F p.1.unop p.2
  map_comp f g :=
    PresheafHom.Endpoints.Map.comp F f.1.unop g.1.unop f.2 g.2

/-- The object map of the endpoint Hom-presheaf functor is the canonical Hom-presheaf. -/
@[simp]
theorem PresheafHom.Endpoints.Functor.obj
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{vP, uP}) (U : C)
    (p : (F.obj (.mk (op U)))ᵒᵖ × F.obj (.mk (op U))) :
    (PresheafHom.Endpoints.functor F U).obj p =
      F.presheafHom p.1.unop p.2 := sorry

/-- The morphism map of the endpoint Hom-presheaf functor is simultaneous endpoint action. -/
@[simp]
theorem PresheafHom.Endpoints.Functor.map
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{vP, uP}) (U : C)
    {p q : (F.obj (.mk (op U)))ᵒᵖ × F.obj (.mk (op U))}
    (f : p ⟶ q) :
    (PresheafHom.Endpoints.functor F U).map f =
      PresheafHom.Endpoints.map F f.1.unop f.2 := sorry

/-- The forward endpoint-conjugation map factors as postcomposition followed by
precomposition. -/
theorem PresheafHom.Congr.Iso.hom
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{vP, uP})
    {U : C} {x₁ x₂ y₁ y₂ : F.obj (.mk (op U))}
    (ex : x₁ ≅ x₂) (ey : y₁ ≅ y₂) :
    (PresheafHom.Congr.iso F ex ey).hom =
      PresheafHom.Postcomp.map F (x := x₁) ey.hom ≫
        PresheafHom.Precomp.map F (z := y₂) ex.inv := sorry

/-- The inverse endpoint-conjugation map factors as inverse postcomposition followed by
inverse precomposition. -/
theorem PresheafHom.Congr.Iso.inv
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{vP, uP})
    {U : C} {x₁ x₂ y₁ y₂ : F.obj (.mk (op U))}
    (ex : x₁ ≅ x₂) (ey : y₁ ≅ y₂) :
    (PresheafHom.Congr.iso F ex ey).inv =
      PresheafHom.Postcomp.map F (x := x₂) ey.inv ≫
        PresheafHom.Precomp.map F (z := y₁) ex.hom := sorry

/-- Conjugation by identity endpoint isomorphisms is the identity Hom-presheaf isomorphism. -/
@[simp]
theorem PresheafHom.Congr.Iso.refl
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{vP, uP})
    {U : C} (x y : F.obj (.mk (op U))) :
    PresheafHom.Congr.iso F (Iso.refl x) (Iso.refl y) =
      Iso.refl (F.presheafHom x y) := sorry

/-- Reversing both endpoint isomorphisms reverses the Hom-presheaf isomorphism. -/
@[simp]
theorem PresheafHom.Congr.Iso.symm
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{vP, uP})
    {U : C} {x₁ x₂ y₁ y₂ : F.obj (.mk (op U))}
    (ex : x₁ ≅ x₂) (ey : y₁ ≅ y₂) :
    (PresheafHom.Congr.iso F ex ey).symm =
      PresheafHom.Congr.iso F ex.symm ey.symm := sorry

/-- Endpoint-conjugation isomorphisms compose along endpoint isomorphisms. -/
theorem PresheafHom.Congr.Iso.trans
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{vP, uP})
    {U : C} {x₁ x₂ x₃ y₁ y₂ y₃ : F.obj (.mk (op U))}
    (ex₁₂ : x₁ ≅ x₂) (ex₂₃ : x₂ ≅ x₃)
    (ey₁₂ : y₁ ≅ y₂) (ey₂₃ : y₂ ≅ y₃) :
    PresheafHom.Congr.iso F ex₁₂ ey₁₂ ≪≫
        PresheafHom.Congr.iso F ex₂₃ ey₂₃ =
      PresheafHom.Congr.iso F (ex₁₂ ≪≫ ex₂₃) (ey₁₂ ≪≫ ey₂₃) := sorry

/-- Endpoint conjugation is the image of the corresponding product isomorphism under the
endpoint Hom-presheaf functor. -/
theorem PresheafHom.Endpoints.Functor.mapIso
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{vP, uP})
    {U : C} {x₁ x₂ y₁ y₂ : F.obj (.mk (op U))}
    (ex : x₁ ≅ x₂) (ey : y₁ ≅ y₂) :
    (PresheafHom.Endpoints.functor F U).mapIso (Iso.prod ex.symm.op ey) =
      PresheafHom.Congr.iso F ex ey := sorry

end Pseudofunctor

end CategoryTheory
