/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Descent.HomPresheaf.StrongTrans

/-!
# Strong-transformation action on canonical Hom-sheaves

A strong transformation between prestacks acts on their canonical Hom-sheaves. The underlying
presheaf morphism is the reusable `Pseudofunctor.StrongTrans.presheafHomMap`; this file only
bundles that map in the full subcategory of sheaves and records its basic functorial API.
-/

@[expose] public section

universe uC vC uP vP

namespace CategoryTheory

open Opposite
open scoped CategoryTheory.Bicategory Pseudofunctor.StrongTrans

namespace Pseudofunctor.StrongTrans

variable {C : Type uC} [Category.{vC} C]
variable {P Q R : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{vP, uP}}

/-- The morphism of canonical Hom-sheaves induced by a strong transformation of prestacks. Its
non-`Prop` map is exactly `presheafHomMap`; sheafness belongs to the source and target owners. -/
def sheafHomMap
    (η : P ⟶ Q) (J : GrothendieckTopology C) [P.IsPrestack J] [Q.IsPrestack J]
    {U : C} (x y : P.obj (LocallyDiscrete.mk (op U))) :
    P.sheafHom J x y ⟶
      Q.sheafHom J
        ((η.app (LocallyDiscrete.mk (op U))).toFunctor.obj x)
        ((η.app (LocallyDiscrete.mk (op U))).toFunctor.obj y) :=
  ObjectProperty.homMk (η.presheafHomMap x y)

/-- Forgetting the Hom-sheaf map recovers the canonical Hom-presheaf map. -/
@[simp]
theorem sheafHomMap_hom
    (η : P ⟶ Q) (J : GrothendieckTopology C) [P.IsPrestack J] [Q.IsPrestack J]
    {U : C} (x y : P.obj (LocallyDiscrete.mk (op U))) :
    (sheafHomMap η J x y).hom = η.presheafHomMap x y := sorry

/-- The identity strong transformation induces the identity map of every Hom-sheaf. -/
@[simp]
theorem sheafHomMap_id
    (P : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{vP, uP})
    (J : GrothendieckTopology C) [P.IsPrestack J]
    {U : C} (x y : P.obj (LocallyDiscrete.mk (op U))) :
    sheafHomMap (𝟙 P) J x y = 𝟙 (P.sheafHom J x y) := sorry

/-- Hom-sheaf maps preserve composition of strong transformations. -/
theorem sheafHomMap_comp
    (η : P ⟶ Q) (θ : Q ⟶ R) (J : GrothendieckTopology C)
    [P.IsPrestack J] [Q.IsPrestack J] [R.IsPrestack J]
    {U : C} (x y : P.obj (LocallyDiscrete.mk (op U))) :
    sheafHomMap (η ≫ θ) J x y =
      sheafHomMap η J x y ≫
        sheafHomMap θ J
          ((η.app (LocallyDiscrete.mk (op U))).toFunctor.obj x)
          ((η.app (LocallyDiscrete.mk (op U))).toFunctor.obj y) := sorry

/-- A canonical Hom-sheaf map is an isomorphism exactly when its underlying Hom-presheaf map
is an isomorphism. -/
theorem sheafHomMap_isIso_iff
    (η : P ⟶ Q) (J : GrothendieckTopology C) [P.IsPrestack J] [Q.IsPrestack J]
    {U : C} (x y : P.obj (LocallyDiscrete.mk (op U))) :
    IsIso (sheafHomMap η J x y) ↔ IsIso (η.presheafHomMap x y) := sorry

/- Axiom audit: `sheafHomMap` stores the explicit `presheafHomMap`; no witness or inverse is
chosen by this sheaf-level wrapper. -/

end Pseudofunctor.StrongTrans

end CategoryTheory
