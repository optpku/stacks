/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.Evaluation.Pseudofunctor.Basic

/-!
# Computations for curried bicategorical evaluation

Base-facing object, morphism, modification, and coherence formulas for the
curried evaluation pseudofunctor.
-/

@[expose] public section

universe wB vB uB wD vD uD

namespace CategoryTheory

open scoped Bicategory Pseudofunctor.StrongTrans

namespace Pseudofunctor

variable {B : Type uB} [Bicategory.{wB, vB} B]
  {D : Type uD} [Bicategory.{wD, vD} D]

section Evaluation

/-- The forward component of the curried-evaluation unit comparison is the evaluated
pseudofunctor's unit comparison. -/
@[simp]
theorem evaluationMapId.hom_app
    (a : B) (F : Pseudofunctor B D) :
    (evaluationMapId D a).hom.as.app F = (F.mapId a).hom := sorry

/-- The inverse component of the curried-evaluation unit comparison is the evaluated
pseudofunctor's inverse unit comparison. -/
@[simp]
theorem evaluationMapId.inv_app
    (a : B) (F : Pseudofunctor B D) :
    (evaluationMapId D a).inv.as.app F = (F.mapId a).inv := sorry

/-- The forward component of the curried-evaluation composition comparison is the
evaluated pseudofunctor's forward composition comparison. -/
@[simp]
theorem evaluationMapComp.hom_app
    {a b c : B} (f : a ⟶ b) (g : b ⟶ c) (F : Pseudofunctor B D) :
    (evaluationMapComp D f g).hom.as.app F = (F.mapComp f g).hom := sorry

/-- The inverse component of the curried-evaluation composition comparison is the
evaluated pseudofunctor's inverse composition comparison. -/
@[simp]
theorem evaluationMapComp.inv_app
    {a b c : B} (f : a ⟶ b) (g : b ⟶ c) (F : Pseudofunctor B D) :
    (evaluationMapComp D f g).inv.as.app F = (F.mapComp f g).inv := sorry

/-- The object action of curried evaluation is the corresponding point-evaluation
pseudofunctor. -/
@[simp]
theorem evaluation.obj (a : B) :
    (evaluation B D).obj a =
      (evaluationAt D a).toPseudofunctor := sorry

/-- The `1`-morphism action of curried evaluation is the corresponding evaluation strong
transformation. -/
@[simp]
theorem evaluation.map
    {a b : B} (f : a ⟶ b) :
    (evaluation B D).map f = evaluationMap D f := sorry

/-- The `2`-morphism action of curried evaluation is the corresponding evaluation
modification. -/
@[simp]
theorem evaluation.map₂
    {a b : B} {f g : a ⟶ b} (η : f ⟶ g) :
    (evaluation B D).map₂ η = evaluationMap₂ D η := sorry

/-- The hom-functor of curried evaluation is the explicit evaluation functor on the source
hom-category. -/
@[simp]
theorem evaluation.mapFunctor (a b : B) :
    (evaluation B D).mapFunctor a b =
      evaluationMapFunctor D a b := sorry

/-- The unit comparison of curried evaluation is the pointwise unit comparison. -/
@[simp]
theorem evaluation.mapId (a : B) :
    (evaluation B D).mapId a = evaluationMapId D a := sorry

/-- The composition comparison of curried evaluation is the pointwise composition
comparison. -/
@[simp]
theorem evaluation.mapComp
    {a b c : B} (f : a ⟶ b) (g : b ⟶ c) :
    (evaluation B D).mapComp f g =
      evaluationMapComp D f g := sorry

/-- Curried evaluation acts on an object twice by ordinary pseudofunctor evaluation. -/
@[simp]
theorem evaluation.at.obj
    (a : B) (F : Pseudofunctor B D) :
    ((evaluation B D).obj a).obj F = F.obj a := sorry

/-- The map of a point-evaluation object is the corresponding component of a strong
transformation. -/
@[simp]
theorem evaluation.at.map
    (a : B) {F G : Pseudofunctor B D} (η : F ⟶ G) :
    ((evaluation B D).obj a).map η = η.app a := sorry

/-- The `2`-morphism map of a point-evaluation object is the corresponding component of a
modification. -/
@[simp]
theorem evaluation.at.map₂
    (a : B) {F G : Pseudofunctor B D} {η θ : F ⟶ G} (Γ : η ⟶ θ) :
    ((evaluation B D).obj a).map₂ Γ = Γ.as.app a := sorry

/-- The hom-functor of a point-evaluation object is component evaluation. -/
@[simp]
theorem evaluation.at.mapFunctor
    (a : B) (F G : Pseudofunctor B D) :
    ((evaluation B D).obj a).mapFunctor F G =
      evaluationHom a F G := sorry

/-- The unit comparison of a point-evaluation object is an identity isomorphism. -/
@[simp]
theorem evaluation.at.mapId
    (a : B) (F : Pseudofunctor B D) :
    ((evaluation B D).obj a).mapId F =
      Iso.refl (𝟙 (F.obj a)) := sorry

/-- The composition comparison of a point-evaluation object is an identity isomorphism. -/
@[simp]
theorem evaluation.at.mapComp
    (a : B) {F G H : Pseudofunctor B D} (η : F ⟶ G) (θ : G ⟶ H) :
    ((evaluation B D).obj a).mapComp η θ =
      Iso.refl (η.app a ≫ θ.app a) := sorry

/-- A `1`-morphism of the source acts at a pseudofunctor by applying its
`1`-morphism map. -/
@[simp]
theorem evaluation.map.app
    {a b : B} (f : a ⟶ b) (F : Pseudofunctor B D) :
    ((evaluation B D).map f).app F = F.map f := sorry

/-- The naturality isomorphism of curried evaluation is inverse strong naturality. -/
@[simp]
theorem evaluation.map.naturality
    {a b : B} (f : a ⟶ b) {F G : Pseudofunctor B D} (η : F ⟶ G) :
    ((evaluation B D).map f).naturality η =
      (η.naturality f).symm := sorry

/-- A `2`-morphism of the source acts at a pseudofunctor by applying its
`2`-morphism map. -/
@[simp]
theorem evaluation.map₂.app
    {a b : B} {f g : a ⟶ b} (γ : f ⟶ g) (F : Pseudofunctor B D) :
    ((evaluation B D).map₂ γ).as.app F = F.map₂ γ := sorry

/-- The forward component of the unit comparison for curried evaluation is pointwise
`Pseudofunctor.mapId`. -/
@[simp]
theorem evaluation.mapId.hom_app
    (a : B) (F : Pseudofunctor B D) :
    ((evaluation B D).mapId a).hom.as.app F =
      (F.mapId a).hom := sorry

/-- The inverse component of the unit comparison for curried evaluation is pointwise
`Pseudofunctor.mapId`. -/
@[simp]
theorem evaluation.mapId.inv_app
    (a : B) (F : Pseudofunctor B D) :
    ((evaluation B D).mapId a).inv.as.app F =
      (F.mapId a).inv := sorry

/-- The forward component of the composition comparison for curried evaluation is pointwise
`Pseudofunctor.mapComp`. -/
@[simp]
theorem evaluation.mapComp.hom_app
    {a b c : B} (f : a ⟶ b) (g : b ⟶ c) (F : Pseudofunctor B D) :
    ((evaluation B D).mapComp f g).hom.as.app F =
      (F.mapComp f g).hom := sorry

/-- The inverse component of the composition comparison for curried evaluation is pointwise
`Pseudofunctor.mapComp`. -/
@[simp]
theorem evaluation.mapComp.inv_app
    {a b c : B} (f : a ⟶ b) (g : b ⟶ c) (F : Pseudofunctor B D) :
    ((evaluation B D).mapComp f g).inv.as.app F =
      (F.mapComp f g).inv := sorry

end Evaluation

end Pseudofunctor

end CategoryTheory
