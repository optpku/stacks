/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.Postcomposition.Pseudofunctor.Basic

/-!
# Hom-functor computations for pseudofunctorial postcomposition

Pointwise formulas for the induced functor on strong-transformation
hom-categories.
-/

@[expose] public section

universe wA vA uA wB vB uB wD vD uD

namespace CategoryTheory

open scoped Bicategory Pseudofunctor.StrongTrans

namespace Pseudofunctor

variable {B : Type uB} [Bicategory.{wB, vB} B]
  {D : Type uD} [Bicategory.{wD, vD} D]

section Postcomposition

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

open scoped Pseudofunctor.StrongTrans

variable {A : Type uA} [Bicategory.{wA, vA} A]

/-- The object action of `postcompHom` has pointwise mapped strong-transformation
components. -/
@[simp]
theorem postcompHom.obj.app
    (K : Pseudofunctor B D) {F G : Pseudofunctor A B}
    (η : F ⟶ G) (a : A) :
    ((postcompHom K F G).obj η).app a = K.map (η.app a) := sorry

/-- The object action of `postcompHom` has the mapped strong-transformation naturality
isomorphism. -/
@[simp]
theorem postcompHom.obj.naturality
    (K : Pseudofunctor B D) {F G : Pseudofunctor A B}
    (η : F ⟶ G) {a b : A} (f : a ⟶ b) :
    ((postcompHom K F G).obj η).naturality f =
      (K.mapComp (F.map f) (η.app b)).symm ≪≫
        K.map₂Iso (η.naturality f) ≪≫
          K.mapComp (η.app a) (G.map f) := sorry

/-- The morphism action of `postcompHom` has pointwise mapped modification components. -/
@[simp]
theorem postcompHom.map.app
    (K : Pseudofunctor B D) {F G : Pseudofunctor A B}
    {η θ : F ⟶ G} (Γ : η ⟶ θ) (a : A) :
    ((postcompHom K F G).map Γ).as.app a = K.map₂ (Γ.as.app a) := sorry

/-- The morphism action of `postcompHom` is the explicitly postcomposed modification. -/
@[simp]
theorem postcompHom.map.naturality
    (K : Pseudofunctor B D) {F G : Pseudofunctor A B}
    {η θ : F ⟶ G} (Γ : η ⟶ θ) {a b : A} (f : a ⟶ b) :
    ((postcompHom K F G).map Γ).as.naturality f =
      (Γ.as.postcomp K).naturality f := sorry

/-- The hom-functor of functor-bicategory postcomposition is the explicit postcomposition
functor on strong transformations and modifications. -/
@[simp]
theorem postcomp.mapFunctor
    (K : Pseudofunctor B D) (F G : Pseudofunctor A B) :
    (postcomp A K).mapFunctor F G = postcompHom K F G := sorry

end Postcomposition

end Pseudofunctor

end CategoryTheory
