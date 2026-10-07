module

public import ReasLib.CategoryTheory.Fibered.ChosenCleavage.Morphism.Modification
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.StrongTrans.Category

/-!
# Hom-category functor for selected fiber strong transformations

For fixed fibred source and target, this module packages the selected fiber
strong-transformation action on morphisms and `2`-morphisms as an ordinary
functor between hom-categories.
-/

@[expose] public section

universe u v uS vS

namespace CategoryTheory

open Bicategory Functor Opposite
open scoped CategoryTheory.Bicategory Pseudofunctor.StrongTrans

namespace FiberedCategoryOver

variable {C : Type u} [Category.{v} C]
variable {X Y : FiberedCategoryOver.{u, v, uS, vS} C}

/-- The hom-category morphism induced by a `2`-morphism of fibred-category morphisms. -/
noncomputable def strongTransMap
    {F G : X ⟶ Y} (τ : F ⟶ G) :
    Pseudofunctor.StrongTrans.Hom
      (strongTrans F) (strongTrans G) :=
  Pseudofunctor.StrongTrans.Hom.of (strongTrans₂ τ)

/-- Forgetting the hom-category wrapper of the induced morphism recovers the underlying fiber
modification. -/
@[simp]
theorem strongTransMap.as
    {F G : X ⟶ Y} (τ : F ⟶ G) :
    (strongTransMap τ).as = strongTrans₂ τ := sorry

/-- The hom-category action on `2`-morphisms preserves identities. -/
@[simp]
theorem strongTransMap.id (F : X ⟶ Y) :
    strongTransMap (𝟙 F) = 𝟙 (strongTrans F) := sorry

/-- The hom-category action on `2`-morphisms preserves vertical composition. -/
@[simp]
theorem strongTransMap.comp
    {F G H : X ⟶ Y} (τ : F ⟶ G) (σ : G ⟶ H) :
    strongTransMap (τ ≫ σ) =
      Pseudofunctor.StrongTrans.Hom.of
        (Pseudofunctor.StrongTrans.Modification.vcomp
          (strongTrans₂ τ) (strongTrans₂ σ)) := sorry

variable (X Y) in
/-- For fixed fibred source and target, passage to selected fiber strong transformations is a
functor on the hom-category.

The endpoints are explicit because this owner has no value input from which Lean can recover the
fixed source and target fibred categories. -/
noncomputable def strongTransHom :
    (X ⟶ Y) ⥤
      Pseudofunctor.StrongTrans
        (Functor.fiberPseudofunctor X.p)
        (Functor.fiberPseudofunctor Y.p) where
    obj F := strongTrans F
    map τ := strongTransMap τ
    map_id F := strongTransMap.id F
    map_comp τ σ := strongTransMap.comp τ σ

/-- The object action of `strongTransHom` is `strongTrans`. -/
@[simp]
theorem strongTransHom.obj (F : X ⟶ Y) :
    (strongTransHom X Y).obj F = strongTrans F := sorry

/-- The morphism action of `strongTransHom` is `strongTransMap`. -/
@[simp]
theorem strongTransHom.map
    {F G : X ⟶ Y} (τ : F ⟶ G) :
    (strongTransHom X Y).map τ = strongTransMap τ := sorry

/-- Forgetting the hom-category wrapper of the map action recovers the selected fiber
modification. -/
@[simp]
theorem strongTransHom.map.as
    {F G : X ⟶ Y} (τ : F ⟶ G) :
    ((strongTransHom X Y).map τ).as = strongTrans₂ τ := sorry

/-- The component of the hom-functor map is the Cat-bundled restriction of the owner
`2`-morphism to the corresponding standard fiber. -/
@[simp]
theorem strongTransHom.map.app
    {F G : X ⟶ Y} (τ : F ⟶ G) (U : LocallyDiscrete Cᵒᵖ) :
    (((strongTransHom X Y).map τ).as.app U) =
      (fiberNatTrans τ (unop U.as)).toCatHom₂ := sorry

/-- The objectwise component of the hom-functor map is the component of the owner
`2`-morphism restricted to the standard fiber. -/
@[simp]
theorem strongTransHom.map.app.component
    {F G : X ⟶ Y} (τ : F ⟶ G) (U : LocallyDiscrete Cᵒᵖ)
    (x : X.p.Fiber (unop U.as)) :
    ((((strongTransHom X Y).map τ).as.app U).toNatTrans.app x) =
      (fiberNatTrans τ (unop U.as)).app x := sorry

/-- Forgetting an objectwise component of the hom-functor map recovers the original
total-category component. -/
@[simp]
theorem strongTransHom.map.app.component.val
    {F G : X ⟶ Y} (τ : F ⟶ G) (U : LocallyDiscrete Cᵒᵖ)
    (x : X.p.Fiber (unop U.as)) :
    (((((strongTransHom X Y).map τ).as.app U).toNatTrans.app x).1) =
      τ.hom.toNatTrans.app x.1 := sorry

/-- The hom-functor sends an identity owner `2`-morphism to the identity morphism of the
corresponding selected fiber strong transformation. -/
@[simp]
theorem strongTransHom.map.id (F : X ⟶ Y) :
    (strongTransHom X Y).map (𝟙 F) = 𝟙 (strongTrans F) := sorry

/-- The hom-functor preserves vertical composition of owner `2`-morphisms. -/
@[simp]
theorem strongTransHom.map.comp
    {F G H : X ⟶ Y} (τ : F ⟶ G) (σ : G ⟶ H) :
    (strongTransHom X Y).map (τ ≫ σ) =
      (strongTransHom X Y).map τ ≫ (strongTransHom X Y).map σ := sorry

end FiberedCategoryOver

end CategoryTheory
