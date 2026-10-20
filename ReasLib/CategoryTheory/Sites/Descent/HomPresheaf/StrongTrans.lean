/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Bicategory.Modification.Pseudo
public import ReasLib.CategoryTheory.Sites.Descent.HomPresheaf.Endpoint.Functoriality

/-!
# Strong-transformation action on canonical Hom-presheaves

A pseudonatural transformation between `Cat`-valued pseudofunctors acts on
every canonical Hom-presheaf by conjugating with its naturality isomorphism.
This file owns the pointwise map, its endpoint naturality, and compatibility
with modifications.
-/

@[expose] public section

universe uC vC uP vP

namespace CategoryTheory

open Opposite
open scoped CategoryTheory.Bicategory Pseudofunctor.StrongTrans

namespace Pseudofunctor

variable {C : Type uC} [Category.{vC} C]

namespace StrongTrans

variable {P Q R : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{vP, uP}}

/-- The map on one value of a Hom-presheaf induced by a strong transformation. It conjugates
the image of a morphism by the pseudonaturality isomorphism. -/
def presheafHomMapApp
    (η : P ⟶ Q) {U : C}
    (x y : P.obj (LocallyDiscrete.mk (op U))) (W : (Over U)ᵒᵖ) :
    (P.presheafHom x y).obj W ⟶
      (Q.presheafHom
        ((η.app (LocallyDiscrete.mk (op U))).toFunctor.obj x)
        ((η.app (LocallyDiscrete.mk (op U))).toFunctor.obj y)).obj W :=
  ↾fun δ ↦
    (η.naturality W.unop.hom.op.toLoc).inv.toNatTrans.app x ≫
      (η.app (LocallyDiscrete.mk (op W.unop.left))).toFunctor.map δ ≫
        (η.naturality W.unop.hom.op.toLoc).hom.toNatTrans.app y

/-- Pointwise naturality of `presheafHomMapApp` in an opposite slice morphism. -/
theorem presheafHomMapApp_naturality_pointwise
    (η : P ⟶ Q) {U : C}
    (x y : P.obj (LocallyDiscrete.mk (op U)))
    {W₁ W₂ : (Over U)ᵒᵖ} (α : W₁ ⟶ W₂)
    (δ : (P.presheafHom x y).obj W₁) :
    ((Q.presheafHom
        ((η.app (LocallyDiscrete.mk (op U))).toFunctor.obj x)
        ((η.app (LocallyDiscrete.mk (op U))).toFunctor.obj y)).map α)
        (presheafHomMapApp η x y W₁ δ) =
      presheafHomMapApp η x y W₂
        (((P.presheafHom x y).map α) δ) := sorry

/-- Naturality of `presheafHomMapApp`, in the form required to construct a natural
transformation of Hom-presheaves. -/
theorem presheafHomMapApp_naturality
    (η : P ⟶ Q) {U : C}
    (x y : P.obj (LocallyDiscrete.mk (op U))) :
    ∀ ⦃W₁ W₂ : (Over U)ᵒᵖ⦄ (α : W₁ ⟶ W₂),
      (P.presheafHom x y).map α ≫ presheafHomMapApp η x y W₂ =
        presheafHomMapApp η x y W₁ ≫
          (Q.presheafHom
            ((η.app (LocallyDiscrete.mk (op U))).toFunctor.obj x)
            ((η.app (LocallyDiscrete.mk (op U))).toFunctor.obj y)).map α := sorry

/-- The natural transformation of Hom-presheaves induced by a strong transformation. -/
def presheafHomMap
    (η : P ⟶ Q) {U : C}
    (x y : P.obj (LocallyDiscrete.mk (op U))) :
    P.presheafHom x y ⟶
      Q.presheafHom
        ((η.app (LocallyDiscrete.mk (op U))).toFunctor.obj x)
        ((η.app (LocallyDiscrete.mk (op U))).toFunctor.obj y) where
  app W := presheafHomMapApp η x y W
  naturality := presheafHomMapApp_naturality η x y

/-- A component of `presheafHomMap` is `presheafHomMapApp`. -/
@[simp]
theorem presheafHomMap_app
    (η : P ⟶ Q) {U : C}
    (x y : P.obj (LocallyDiscrete.mk (op U))) (W : (Over U)ᵒᵖ) :
    (presheafHomMap η x y).app W = presheafHomMapApp η x y W := rfl

/-- Evaluation of `presheafHomMap` is conjugation by the pseudonaturality isomorphism. -/
@[simp]
theorem presheafHomMap_app_apply
    (η : P ⟶ Q) {U : C}
    (x y : P.obj (LocallyDiscrete.mk (op U))) (W : (Over U)ᵒᵖ)
    (δ : (P.presheafHom x y).obj W) :
    (presheafHomMap η x y).app W δ =
      (η.naturality W.unop.hom.op.toLoc).inv.toNatTrans.app x ≫
        (η.app (LocallyDiscrete.mk (op W.unop.left))).toFunctor.map δ ≫
          (η.naturality W.unop.hom.op.toLoc).hom.toNatTrans.app y := rfl

/-- The identity strong transformation induces the identity map of every Hom-presheaf. -/
@[simp]
theorem presheafHomMap_id
    (P : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{vP, uP})
    {U : C} (x y : P.obj (LocallyDiscrete.mk (op U))) :
    presheafHomMap (𝟙 P) x y = 𝟙 (P.presheafHom x y) := sorry

/-- The Hom-presheaf map induced by a composite strong transformation is the composite of the
two induced Hom-presheaf maps. -/
theorem presheafHomMap_comp
    (η : P ⟶ Q) (θ : Q ⟶ R) {U : C}
    (x y : P.obj (LocallyDiscrete.mk (op U))) :
    presheafHomMap (η ≫ θ) x y =
      presheafHomMap η x y ≫
        presheafHomMap θ
          ((η.app (LocallyDiscrete.mk (op U))).toFunctor.obj x)
          ((η.app (LocallyDiscrete.mk (op U))).toFunctor.obj y) := sorry

/-- Pointwise computation of the Hom-presheaf map induced by a composite strong
transformation. -/
theorem presheafHomMap_comp_app_apply
    (η : P ⟶ Q) (θ : Q ⟶ R) {U : C}
    (x y : P.obj (LocallyDiscrete.mk (op U)))
    (W : (Over U)ᵒᵖ) (δ : (P.presheafHom x y).obj W) :
    (presheafHomMap (η ≫ θ) x y).app W δ =
      (presheafHomMap θ
        ((η.app (LocallyDiscrete.mk (op U))).toFunctor.obj x)
        ((η.app (LocallyDiscrete.mk (op U))).toFunctor.obj y)).app W
          ((presheafHomMap η x y).app W δ) := sorry

/-- `presheafHomMapApp` is natural in isomorphisms of both endpoint objects. -/
theorem presheafHomMapApp_natural_of_iso
    (η : P ⟶ Q) {U : C} {x₁ x₂ y₁ y₂ : P.obj (LocallyDiscrete.mk (op U))}
    (ex : x₁ ≅ x₂) (ey : y₁ ≅ y₂) (W : (Over U)ᵒᵖ)
    (δ : (P.presheafHom x₁ y₁).obj W) :
    presheafHomMapApp η x₂ y₂ W
        (Iso.homCongr
          ((P.map W.unop.hom.op.toLoc).toFunctor.mapIso ex)
          ((P.map W.unop.hom.op.toLoc).toFunctor.mapIso ey) δ) =
      Iso.homCongr
          ((Q.map W.unop.hom.op.toLoc).toFunctor.mapIso
            ((η.app (LocallyDiscrete.mk (op U))).toFunctor.mapIso ex))
          ((Q.map W.unop.hom.op.toLoc).toFunctor.mapIso
            ((η.app (LocallyDiscrete.mk (op U))).toFunctor.mapIso ey))
        (presheafHomMapApp η x₁ y₁ W δ) := sorry

/-- The Hom-presheaf component of a strong transformation commutes with postcomposition. -/
theorem presheafHomMapApp_postcomp
    (η : P ⟶ Q) {U : C}
    {x y z : P.obj (LocallyDiscrete.mk (op U))} (ψ : y ⟶ z)
    (W : (Over U)ᵒᵖ) (δ : (P.presheafHom x y).obj W) :
    presheafHomMapApp η x y W δ ≫
        (Q.map W.unop.hom.op.toLoc).toFunctor.map
          ((η.app (LocallyDiscrete.mk (op U))).toFunctor.map ψ) =
      presheafHomMapApp η x z W
        (δ ≫ (P.map W.unop.hom.op.toLoc).toFunctor.map ψ) := sorry

/-- The Hom-presheaf component of a strong transformation commutes with precomposition. -/
theorem presheafHomMapApp_precomp
    (η : P ⟶ Q) {U : C}
    {x y z : P.obj (LocallyDiscrete.mk (op U))} (φ : x ⟶ y)
    (W : (Over U)ᵒᵖ) (δ : (P.presheafHom y z).obj W) :
    (Q.map W.unop.hom.op.toLoc).toFunctor.map
          ((η.app (LocallyDiscrete.mk (op U))).toFunctor.map φ) ≫
        presheafHomMapApp η y z W δ =
      presheafHomMapApp η x z W
        ((P.map W.unop.hom.op.toLoc).toFunctor.map φ ≫ δ) := sorry

/-- Hom-presheaf maps induced by strong transformations are compatible with a modification.
Pointwise, the modification acts at both endpoint objects. -/
theorem presheafHomMapApp_natural_of_modification
    {η θ : P ⟶ Q} (Γ : Modification η θ) {U : C}
    (x y : P.obj (LocallyDiscrete.mk (op U))) (W : (Over U)ᵒᵖ)
    (δ : (P.presheafHom x y).obj W) :
    presheafHomMapApp η x y W δ ≫
        (Q.map W.unop.hom.op.toLoc).toFunctor.map
          ((Γ.app (LocallyDiscrete.mk (op U))).toNatTrans.app y) =
      (Q.map W.unop.hom.op.toLoc).toFunctor.map
          ((Γ.app (LocallyDiscrete.mk (op U))).toNatTrans.app x) ≫
        presheafHomMapApp θ x y W δ := sorry

/-- A strong transformation commutes with endpoint conjugation, as an equality of natural
transformations of Hom-presheaves. -/
theorem presheafHomMap_natural_of_iso
    (η : P ⟶ Q) {U : C} {x₁ x₂ y₁ y₂ : P.obj (LocallyDiscrete.mk (op U))}
    (ex : x₁ ≅ x₂) (ey : y₁ ≅ y₂) :
    (Pseudofunctor.PresheafHom.Congr.iso P ex ey).hom ≫
        presheafHomMap η x₂ y₂ =
      presheafHomMap η x₁ y₁ ≫
        (Pseudofunctor.PresheafHom.Congr.iso Q
          ((η.app (LocallyDiscrete.mk (op U))).toFunctor.mapIso ex)
          ((η.app (LocallyDiscrete.mk (op U))).toFunctor.mapIso ey)).hom := sorry

/-- The Hom-presheaf map of a strong transformation commutes with postcomposition. -/
theorem presheafHomMap_postcomp
    (η : P ⟶ Q) {U : C}
    {x y z : P.obj (LocallyDiscrete.mk (op U))} (ψ : y ⟶ z) :
    presheafHomMap η x y ≫
        Pseudofunctor.PresheafHom.Postcomp.map Q
          ((η.app (LocallyDiscrete.mk (op U))).toFunctor.map ψ) =
      Pseudofunctor.PresheafHom.Postcomp.map P ψ ≫
        presheafHomMap η x z := sorry

/-- The Hom-presheaf map of a strong transformation commutes with precomposition. -/
theorem presheafHomMap_precomp
    (η : P ⟶ Q) {U : C}
    {x y z : P.obj (LocallyDiscrete.mk (op U))} (φ : x ⟶ y) :
    presheafHomMap η y z ≫
        Pseudofunctor.PresheafHom.Precomp.map Q
          ((η.app (LocallyDiscrete.mk (op U))).toFunctor.map φ) =
      Pseudofunctor.PresheafHom.Precomp.map P φ ≫
        presheafHomMap η x z := sorry

/-- The Hom-presheaf map of a strong transformation is natural in arbitrary morphisms of both
endpoint objects. -/
theorem presheafHomMap_mapEndpoints
    (η : P ⟶ Q) {U : C}
    {x₁ x₂ y₁ y₂ : P.obj (LocallyDiscrete.mk (op U))}
    (φ : x₂ ⟶ x₁) (ψ : y₁ ⟶ y₂) :
    Pseudofunctor.PresheafHom.Endpoints.map P φ ψ ≫
        presheafHomMap η x₂ y₂ =
      presheafHomMap η x₁ y₁ ≫
        Pseudofunctor.PresheafHom.Endpoints.map Q
          ((η.app (LocallyDiscrete.mk (op U))).toFunctor.map φ)
          ((η.app (LocallyDiscrete.mk (op U))).toFunctor.map ψ) := sorry

/-- A strong transformation induces a natural transformation between the endpoint
Hom-presheaf functors. -/
def presheafHomNatTrans
    (η : P ⟶ Q) (U : C) :
    Pseudofunctor.PresheafHom.Endpoints.functor P U ⟶
      ((η.app (LocallyDiscrete.mk (op U))).toFunctor.op.prod
          (η.app (LocallyDiscrete.mk (op U))).toFunctor) ⋙
        Pseudofunctor.PresheafHom.Endpoints.functor Q U where
  app p := presheafHomMap η p.1.unop p.2
  naturality := fun {_ _} f ↦
    presheafHomMap_mapEndpoints η f.1.unop f.2

/-- A component of the endpoint-natural Hom-presheaf transformation is the canonical map on
the corresponding Hom-presheaf. -/
@[simp]
theorem presheafHomNatTrans_app
    (η : P ⟶ Q) (U : C)
    (p : (P.obj (LocallyDiscrete.mk (op U)))ᵒᵖ ×
      P.obj (LocallyDiscrete.mk (op U))) :
    (presheafHomNatTrans η U).app p =
      presheafHomMap η p.1.unop p.2 := rfl

/-- Hom-presheaf maps induced by two strong transformations are compatible with a modification,
as an equality of natural transformations. -/
theorem presheafHomMap_natural_of_modification
    {η θ : P ⟶ Q} (Γ : Modification η θ) {U : C}
    (x y : P.obj (LocallyDiscrete.mk (op U))) :
    presheafHomMap η x y ≫
        Pseudofunctor.PresheafHom.Postcomp.map Q
          ((Γ.app (LocallyDiscrete.mk (op U))).toNatTrans.app y) =
      presheafHomMap θ x y ≫
        Pseudofunctor.PresheafHom.Precomp.map Q
          ((Γ.app (LocallyDiscrete.mk (op U))).toNatTrans.app x) := sorry

end StrongTrans

end Pseudofunctor

end CategoryTheory
