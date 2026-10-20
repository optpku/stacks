module

public import Mathlib.CategoryTheory.Bicategory.Functor.StrictPseudofunctor
public import Mathlib.CategoryTheory.Bicategory.FunctorBicategory.Pseudo

/-!
# Point evaluation of pseudofunctors

The strict pseudofunctor obtained by evaluating pseudofunctors and strong
transformations at one fixed source object. Computation rules live in
`Evaluation.At.Computations`.
-/

@[expose] public section

universe wB vB uB wD vD uD

namespace CategoryTheory

open scoped Bicategory Pseudofunctor.StrongTrans

namespace Pseudofunctor

variable {B : Type uB} [Bicategory.{wB, vB} B]
  {D : Type uD} [Bicategory.{wD, vD} D]

section Evaluation

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-- The object part of evaluation at a fixed object of the source bicategory. -/
private def evaluationAtObj (a : B) (F : Pseudofunctor B D) : D :=
  F.obj a

/-- The 1-morphism part of evaluation at a fixed object of the source bicategory. -/
private def evaluationAtMap
    (a : B) {F G : Pseudofunctor B D} (η : F ⟶ G) :
    evaluationAtObj a F ⟶ evaluationAtObj a G :=
  η.app a

/-- The 2-morphism part of evaluation at a fixed object of the source bicategory. -/
private def evaluationAtMap₂
    (a : B) {F G : Pseudofunctor B D} {η θ : F ⟶ G} (Γ : η ⟶ θ) :
    evaluationAtMap a η ⟶ evaluationAtMap a θ :=
  Γ.as.app a

/-- Evaluation at a fixed object preserves identity modifications. -/
private theorem evaluationAtMap₂_id
    (a : B) {F G : Pseudofunctor B D} (η : F ⟶ G) :
    evaluationAtMap₂ a (𝟙 η) = 𝟙 (evaluationAtMap a η) := sorry

/-- Evaluation at a fixed object preserves vertical composition of modifications. -/
private theorem evaluationAtMap₂_comp
    (a : B) {F G : Pseudofunctor B D} {η θ ι : F ⟶ G}
    (Γ : η ⟶ θ) (Δ : θ ⟶ ι) :
    evaluationAtMap₂ a (Γ ≫ Δ) =
      evaluationAtMap₂ a Γ ≫ evaluationAtMap₂ a Δ := sorry

/-- Evaluation at `a` on the hom-category between two pseudofunctors. Its objects are
components of strong transformations and its morphisms are components of modifications. -/
def evaluationHom (a : B) (F G : Pseudofunctor B D) :
    (F ⟶ G) ⥤ (F.obj a ⟶ G.obj a) where
  obj := evaluationAtMap a
  map := evaluationAtMap₂ a
  map_id := evaluationAtMap₂_id a
  map_comp := evaluationAtMap₂_comp a

/-- The identity comparison used by evaluation at a fixed object. -/
private def evaluationAtMapId (a : B) (F : Pseudofunctor B D) :
    evaluationAtMap a (𝟙 F) ≅ 𝟙 (evaluationAtObj a F) :=
  Iso.refl _

/-- The composition comparison used by evaluation at a fixed object. -/
private def evaluationAtMapComp
    (a : B) {F G H : Pseudofunctor B D} (η : F ⟶ G) (θ : G ⟶ H) :
    evaluationAtMap a (η ≫ θ) ≅ evaluationAtMap a η ≫ evaluationAtMap a θ :=
  Iso.refl _

/-- Evaluation strictly preserves identity 1-morphisms. -/
private theorem evaluationAtMap_id
    (a : B) (F : Pseudofunctor B D) :
    evaluationAtMap a (𝟙 F) = 𝟙 (evaluationAtObj a F) := sorry

/-- The identity comparison of evaluation is induced by its strict identity equation. -/
private theorem evaluationAtMapId_eq_eqToIso
    (a : B) (F : Pseudofunctor B D) :
    evaluationAtMapId a F = eqToIso (evaluationAtMap_id a F) := sorry

/-- Evaluation strictly preserves composition of 1-morphisms. -/
private theorem evaluationAtMap_comp
    (a : B) {F G H : Pseudofunctor B D} (η : F ⟶ G) (θ : G ⟶ H) :
    evaluationAtMap a (η ≫ θ) =
      evaluationAtMap a η ≫ evaluationAtMap a θ := sorry

/-- The composition comparison of evaluation is induced by its strict composition equation. -/
private theorem evaluationAtMapComp_eq_eqToIso
    (a : B) {F G H : Pseudofunctor B D} (η : F ⟶ G) (θ : G ⟶ H) :
    evaluationAtMapComp a η θ = eqToIso (evaluationAtMap_comp a η θ) := sorry

/-- Evaluation is compatible with left whiskering in the functor bicategory. -/
private theorem evaluationAtMap₂_whisker_left
    (a : B) {F G H : Pseudofunctor B D} (η : F ⟶ G)
    {θ ι : G ⟶ H} (Γ : θ ⟶ ι) :
    evaluationAtMap₂ a (η ◁ Γ) =
      (evaluationAtMapComp a η θ).hom ≫
        evaluationAtMap a η ◁ evaluationAtMap₂ a Γ ≫
        (evaluationAtMapComp a η ι).inv := sorry

/-- Evaluation is compatible with right whiskering in the functor bicategory. -/
private theorem evaluationAtMap₂_whisker_right
    (a : B) {F G H : Pseudofunctor B D} {η θ : F ⟶ G}
    (Γ : η ⟶ θ) (ι : G ⟶ H) :
    evaluationAtMap₂ a (Γ ▷ ι) =
      (evaluationAtMapComp a η ι).hom ≫
        evaluationAtMap₂ a Γ ▷ evaluationAtMap a ι ≫
        (evaluationAtMapComp a θ ι).inv := sorry

/-- Evaluation is compatible with the left unitor of the functor bicategory. -/
private theorem evaluationAtMap₂_left_unitor
    (a : B) {F G : Pseudofunctor B D} (η : F ⟶ G) :
    evaluationAtMap₂ a (λ_ η).hom =
      (evaluationAtMapComp a (𝟙 F) η).hom ≫
        (evaluationAtMapId a F).hom ▷ evaluationAtMap a η ≫
        (λ_ (evaluationAtMap a η)).hom := sorry

/-- Evaluation is compatible with the right unitor of the functor bicategory. -/
private theorem evaluationAtMap₂_right_unitor
    (a : B) {F G : Pseudofunctor B D} (η : F ⟶ G) :
    evaluationAtMap₂ a (ρ_ η).hom =
      (evaluationAtMapComp a η (𝟙 G)).hom ≫
        evaluationAtMap a η ◁ (evaluationAtMapId a G).hom ≫
        (ρ_ (evaluationAtMap a η)).hom := sorry

/-- Evaluation is compatible with the associator of the functor bicategory. -/
private theorem evaluationAtMap₂_associator
    (a : B) {F G H I : Pseudofunctor B D}
    (η : F ⟶ G) (θ : G ⟶ H) (ι : H ⟶ I) :
    evaluationAtMap₂ a (α_ η θ ι).hom =
      (evaluationAtMapComp a (η ≫ θ) ι).hom ≫
        (evaluationAtMapComp a η θ).hom ▷ evaluationAtMap a ι ≫
        (α_ (evaluationAtMap a η) (evaluationAtMap a θ)
          (evaluationAtMap a ι)).hom ≫
        evaluationAtMap a η ◁ (evaluationAtMapComp a θ ι).inv ≫
        (evaluationAtMapComp a η (θ ≫ ι)).inv := sorry

variable (D) in
/-- Evaluation at an object of the source is a strict pseudofunctor from the functor
bicategory. This is the common owner behind pointwise projection pseudofunctors. The target
bicategory `D` is explicit because the source object alone does not determine it. -/
def evaluationAt (a : B) :
    StrictPseudofunctor (Pseudofunctor B D) D where
  obj := evaluationAtObj a
  map := evaluationAtMap a
  map₂ := evaluationAtMap₂ a
  map₂_id := evaluationAtMap₂_id a
  map₂_comp := evaluationAtMap₂_comp a
  mapId := evaluationAtMapId a
  mapComp := evaluationAtMapComp a
  map₂_whisker_left := evaluationAtMap₂_whisker_left a
  map₂_whisker_right := evaluationAtMap₂_whisker_right a
  map₂_left_unitor := evaluationAtMap₂_left_unitor a
  map₂_right_unitor := evaluationAtMap₂_right_unitor a
  map₂_associator := evaluationAtMap₂_associator a
  map_id := evaluationAtMap_id a
  mapId_eq_eqToIso := evaluationAtMapId_eq_eqToIso a
  map_comp := evaluationAtMap_comp a
  mapComp_eq_eqToIso := evaluationAtMapComp_eq_eqToIso a

end Evaluation

end Pseudofunctor

end CategoryTheory
