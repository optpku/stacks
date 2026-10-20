/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.Evaluation.At.Basic

/-!
# Computations for point evaluation

Projection formulas for the strict point-evaluation pseudofunctor and its
hom-category action.
-/

@[expose] public section

universe wB vB uB wD vD uD

namespace CategoryTheory

open scoped Bicategory Pseudofunctor.StrongTrans

namespace Pseudofunctor

variable {B : Type uB} [Bicategory.{wB, vB} B]
  {D : Type uD} [Bicategory.{wD, vD} D]

section Evaluation

/-- On objects, hom-category evaluation takes the component of a strong transformation. -/
@[simp]
theorem evaluationHom.obj
    (a : B) {F G : Pseudofunctor B D} (η : F ⟶ G) :
    (evaluationHom a F G).obj η = η.app a := sorry

/-- On morphisms, hom-category evaluation takes the component of a modification. -/
@[simp]
theorem evaluationHom.map
    (a : B) {F G : Pseudofunctor B D} {η θ : F ⟶ G} (Γ : η ⟶ θ) :
    (evaluationHom a F G).map Γ = Γ.as.app a := sorry

/-- Evaluation computes on objects by applying the pseudofunctor at the chosen source object. -/
@[simp]
theorem evaluationAt.obj (a : B) (F : Pseudofunctor B D) :
    (evaluationAt D a).obj F = F.obj a := sorry

/-- Evaluation computes on 1-morphisms by taking components of strong transformations. -/
@[simp]
theorem evaluationAt.map
    (a : B) {F G : Pseudofunctor B D} (η : F ⟶ G) :
    (evaluationAt D a).map η = η.app a := sorry

/-- Evaluation computes on 2-morphisms by taking components of modifications. -/
@[simp]
theorem evaluationAt.map₂
    (a : B) {F G : Pseudofunctor B D} {η θ : F ⟶ G} (Γ : η ⟶ θ) :
    (evaluationAt D a).map₂ Γ = Γ.as.app a := sorry

/-- The hom-functor of evaluation is the explicit component-evaluation functor. -/
@[simp]
theorem evaluationAt.mapFunctor
    (a : B) (F G : Pseudofunctor B D) :
    (evaluationAt D a).mapFunctor F G = evaluationHom a F G := sorry

/-- Evaluation sends an identity strong transformation to the identity component. -/
@[simp]
theorem evaluationAt.map_id
    (a : B) (F : Pseudofunctor B D) :
    (evaluationAt D a).map (𝟙 F) = 𝟙 (F.obj a) := sorry

/-- Evaluation sends a composite of strong transformations to the composite of components. -/
@[simp]
theorem evaluationAt.map_comp
    (a : B) {F G H : Pseudofunctor B D} (η : F ⟶ G) (θ : G ⟶ H) :
    (evaluationAt D a).map (η ≫ θ) = η.app a ≫ θ.app a := sorry

/-- The identity comparison of evaluation is the identity component isomorphism. -/
@[simp]
theorem evaluationAt.mapId (a : B) (F : Pseudofunctor B D) :
    (evaluationAt D a).mapId F = Iso.refl (𝟙 (F.obj a)) := sorry

/-- The composition comparison of evaluation is the identity component isomorphism. -/
@[simp]
theorem evaluationAt.mapComp
    (a : B) {F G H : Pseudofunctor B D} (η : F ⟶ G) (θ : G ⟶ H) :
    (evaluationAt D a).mapComp η θ = Iso.refl (η.app a ≫ θ.app a) := sorry

end Evaluation

end Pseudofunctor

end CategoryTheory
