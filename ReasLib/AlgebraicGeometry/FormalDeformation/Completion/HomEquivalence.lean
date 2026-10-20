/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Completion.Unit

@[expose] public section

open CategoryTheory ArtinianLocalAlgCat
open scoped BasedFunctor

noncomputable section

universe u v

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CategoryTheory.CofiberedCategoryOver.Groupoids

open BasedCategory

variable
  (F : CofiberedCategoryOver.Groupoids.{u + 1, u, v, v} (ArtinianLocalAlgCat Λ k))
  (G : CofiberedCategoryOver.Groupoids.{u + 1, u, max (u + 1) v, max u v}
    (CompleteLocalAlgCat Λ k))

set_option backward.privateInPublic true

/-- Stagewise application of a based functor preserves truncation bases and transition lifts. -/
theorem completionMap_obj_laws
    (φ : (restrictInclusion G).toBasedCategory ⥤ᵇ F.toBasedCategory)
    (ξ : FormalObject (RestrictInclusion.projectionTotal G.toBasedCategory)) :
    (∀ n, F.p.obj (φ.obj (ULiftHom.objDown (ξ.system.family n))) = ξ.base.truncation n) ∧
    (∀ n, F.p.IsHomLift (ξ.base.truncationMap n)
      (φ.map (ULiftHom.down.map (ξ.system.stepMap n)))) := sorry
private def completionMapObj
    (φ : (restrictInclusion G).toBasedCategory ⥤ᵇ F.toBasedCategory)
    (ξ : FormalObject (RestrictInclusion.projectionTotal G.toBasedCategory)) : FormalObject F.p :=
  FormalObject.of ξ.base
    (fun n ↦ φ.obj (ULiftHom.objDown (ξ.system.family n)))
    (fun n ↦ φ.map (ULiftHom.down.map (ξ.system.stepMap n)))
    (completionMap_obj_laws F G φ ξ).1 (completionMap_obj_laws F G φ ξ).2

/-- Stagewise application preserves lifted arrows and their compatibility with transitions. -/
theorem completionMap_map_laws
    (φ : (restrictInclusion G).toBasedCategory ⥤ᵇ F.toBasedCategory)
    {ξ η : FormalObject (RestrictInclusion.projectionTotal G.toBasedCategory)} (a : ξ ⟶ η) :
    (∀ n, F.p.IsHomLift (a.baseTrunc n) (φ.map (ULiftHom.down.map (a.app n)))) ∧
    (∀ n, (completionMapObj F G φ ξ).system.stepMap n ≫
      φ.map (ULiftHom.down.map (a.app n)) =
      φ.map (ULiftHom.down.map (a.app (n + 1))) ≫
        (completionMapObj F G φ η).system.stepMap n) := sorry
private def completionMapMap
    (φ : (restrictInclusion G).toBasedCategory ⥤ᵇ F.toBasedCategory)
    {ξ η : FormalObject (RestrictInclusion.projectionTotal G.toBasedCategory)} (a : ξ ⟶ η) :
    completionMapObj F G φ ξ ⟶ completionMapObj F G φ η :=
  FormalObject.Hom.of a.base (fun n ↦ φ.map (ULiftHom.down.map (a.app n))) a.baseTrunc
    (completionMap_map_laws F G φ a).1 a.baseTrunc_spec (completionMap_map_laws F G φ a).2

/-- Stagewise completion preserves identities and composition. -/
theorem completionMap_functor_laws
    (φ : (restrictInclusion G).toBasedCategory ⥤ᵇ F.toBasedCategory) :
    (∀ ξ, completionMapMap F G φ (𝟙 ξ) = 𝟙 (completionMapObj F G φ ξ)) ∧
    (∀ (ξ η ζ : FormalObject (RestrictInclusion.projectionTotal G.toBasedCategory))
      (a : ξ ⟶ η) (b : η ⟶ ζ),
      completionMapMap F G φ (a ≫ b) = completionMapMap F G φ a ≫ completionMapMap F G φ b) := sorry
private def completionMapFunctor
    (φ : (restrictInclusion G).toBasedCategory ⥤ᵇ F.toBasedCategory) :
    FormalObject (RestrictInclusion.projectionTotal G.toBasedCategory) ⥤ FormalObject F.p where
  obj := completionMapObj F G φ
  map := completionMapMap F G φ
  map_id := (completionMap_functor_laws F G φ).1
  map_comp := (completionMap_functor_laws F G φ).2 _ _ _
/-- Stagewise completion commutes with the complete local projection. -/
theorem completionMap_w
    (φ : (restrictInclusion G).toBasedCategory ⥤ᵇ F.toBasedCategory) :
    completionMapFunctor F G φ ⋙ Functor.completion F.p =
      Functor.completion (RestrictInclusion.projectionTotal G.toBasedCategory) := sorry
/-- Apply a based functor stagewise to the completion of a lifted restriction. -/
def completionMap (φ : (restrictInclusion G).toBasedCategory ⥤ᵇ F.toBasedCategory) :
    BasedCategory.ofFunctor
      (Functor.completion (RestrictInclusion.projectionTotal G.toBasedCategory)) ⥤ᵇ
        BasedCategory.ofFunctor (Functor.completion F.p) where
  toFunctor := completionMapFunctor F G φ
  w := completionMap_w F G φ

private def completionMap₂AppLaws
    {φ ψ : (restrictInclusion G).toBasedCategory ⥤ᵇ F.toBasedCategory} (t : φ ⟶ ψ) : Prop :=
  ∀ ξ : FormalObject (RestrictInclusion.projectionTotal G.toBasedCategory),
    (∀ n, F.p.IsHomLift (𝟙 (ξ.base.truncation n))
      (t.toNatTrans.app (ULiftHom.objDown (ξ.system.family n)))) ∧
    (∀ n, (ArtinianLocalAlgCat.Hom.toRingHom (𝟙 (ξ.base.truncation n))).comp
      (Ideal.Quotient.mk (CompleteLocalAlgCat.maximalIdeal ξ.base ^ (n + 1))) =
      (Ideal.Quotient.mk (CompleteLocalAlgCat.maximalIdeal ξ.base ^ (n + 1))).comp
        (CompleteLocalAlgCat.Hom.toRingHom (𝟙 ξ.base))) ∧
    (∀ n, ((completionMap F G φ).obj ξ).system.stepMap n ≫
      t.toNatTrans.app (ULiftHom.objDown (ξ.system.family n)) =
      t.toNatTrans.app (ULiftHom.objDown (ξ.system.family (n + 1))) ≫
        ((completionMap F G ψ).obj ξ).system.stepMap n)
private def completionMap₂AppRaw
    {φ ψ : (restrictInclusion G).toBasedCategory ⥤ᵇ F.toBasedCategory} (t : φ ⟶ ψ)
    (h : completionMap₂AppLaws F G t)
    (ξ : FormalObject (RestrictInclusion.projectionTotal G.toBasedCategory)) :
    (completionMap F G φ).obj ξ ⟶ (completionMap F G ψ).obj ξ :=
  FormalObject.Hom.of (𝟙 ξ.base)
    (fun n ↦ t.toNatTrans.app (ULiftHom.objDown (ξ.system.family n)))
    (fun n ↦ 𝟙 (ξ.base.truncation n)) (h ξ).1 (h ξ).2.1 (h ξ).2.2
/-- Stagewise application of a vertical transformation is natural and vertical. -/
theorem completionMap₂_laws
    {φ ψ : (restrictInclusion G).toBasedCategory ⥤ᵇ F.toBasedCategory} (t : φ ⟶ ψ) :
    completionMap₂AppLaws F G t ∧
    (∀ h : completionMap₂AppLaws F G t,
      (∀ (ξ η : FormalObject (RestrictInclusion.projectionTotal G.toBasedCategory)) (a : ξ ⟶ η),
        (completionMap F G φ).map a ≫ completionMap₂AppRaw F G t h η =
          completionMap₂AppRaw F G t h ξ ≫ (completionMap F G ψ).map a) ∧
      (∀ ξ, (Functor.completion F.p).IsHomLift (𝟙 ξ.base) (completionMap₂AppRaw F G t h ξ))) := sorry
/-- Apply a vertical natural transformation stagewise to formal objects. -/
def completionMap₂ {φ ψ : (restrictInclusion G).toBasedCategory ⥤ᵇ F.toBasedCategory}
    (t : φ ⟶ ψ) : completionMap F G φ ⟶ completionMap F G ψ where
  toNatTrans :=
    { app := completionMap₂AppRaw F G t (completionMap₂_laws F G t).1
      naturality := fun {ξ η} a ↦
        ((completionMap₂_laws F G t).2 (completionMap₂_laws F G t).1).1 ξ η a }
  isHomLift' := ((completionMap₂_laws F G t).2 (completionMap₂_laws F G t).1).2

/-- Whiskering the stagewise completion with the unit preserves identities and composition. -/
theorem homEquivFunctor_laws :
    (∀ φ : (restrictInclusion G).toBasedCategory ⥤ᵇ F.toBasedCategory,
      BasedCategory.whiskerLeft (completionUnit G) (completionMap₂ F G (𝟙 φ)) =
        𝟙 (BasedFunctor.comp (completionUnit G) (completionMap F G φ))) ∧
    (∀ (φ ψ χ : (restrictInclusion G).toBasedCategory ⥤ᵇ F.toBasedCategory)
      (t : φ ⟶ ψ) (s : ψ ⟶ χ),
      BasedCategory.whiskerLeft (completionUnit G) (completionMap₂ F G (t ≫ s)) =
        BasedCategory.whiskerLeft (completionUnit G) (completionMap₂ F G t) ≫
          BasedCategory.whiskerLeft (completionUnit G) (completionMap₂ F G s)) := sorry
/-- Compose the truncation-pushforward unit with the stagewise completion of a based functor. -/
def homEquivFunctor :
    ((restrictInclusion G).toBasedCategory ⥤ᵇ F.toBasedCategory) ⥤
      (G.toBasedCategory ⥤ᵇ BasedCategory.ofFunctor (Functor.completion F.p)) where
  obj φ := BasedFunctor.comp (completionUnit G) (completionMap F G φ)
  map t := BasedCategory.whiskerLeft (completionUnit G) (completionMap₂ F G t)
  map_id := (homEquivFunctor_laws F G).1
  map_comp := (homEquivFunctor_laws F G).2 _ _ _
/-- The forward hom-functor composes the unit with the completed morphism. -/
theorem homEquivFunctor_obj
    (φ : (restrictInclusion G).toBasedCategory ⥤ᵇ F.toBasedCategory) :
    (homEquivFunctor F G).obj φ =
      BasedFunctor.comp (completionUnit G) (completionMap F G φ) := rfl

/-- Restriction followed by whiskering with evaluation preserves identities and composition. -/
theorem homEquivInverse_laws :
    (∀ ψ : G.toBasedCategory ⥤ᵇ BasedCategory.ofFunctor (Functor.completion F.p),
      BasedCategory.whiskerRight (RestrictInclusion.map₂ (𝟙 ψ)) (completionCounit F) =
        𝟙 (BasedFunctor.comp (RestrictInclusion.map ψ) (completionCounit F))) ∧
    (∀ (ψ χ ω : G.toBasedCategory ⥤ᵇ BasedCategory.ofFunctor (Functor.completion F.p))
      (t : ψ ⟶ χ) (s : χ ⟶ ω),
      BasedCategory.whiskerRight (RestrictInclusion.map₂ (t ≫ s)) (completionCounit F) =
        BasedCategory.whiskerRight (RestrictInclusion.map₂ t) (completionCounit F) ≫
          BasedCategory.whiskerRight (RestrictInclusion.map₂ s) (completionCounit F)) := sorry
/-- Restrict a morphism to Artinian bases and then apply canonical evaluation. -/
def homEquivInverse :
    (G.toBasedCategory ⥤ᵇ BasedCategory.ofFunctor (Functor.completion F.p)) ⥤
      ((restrictInclusion G).toBasedCategory ⥤ᵇ F.toBasedCategory) where
  obj ψ := BasedFunctor.comp (RestrictInclusion.map ψ) (completionCounit F)
  map t := BasedCategory.whiskerRight (RestrictInclusion.map₂ t) (completionCounit F)
  map_id := (homEquivInverse_laws F G).1
  map_comp := (homEquivInverse_laws F G).2 _ _ _
/-- The inverse hom-functor restricts the morphism and composes with the counit. -/
theorem homEquivInverse_obj
    (ψ : G.toBasedCategory ⥤ᵇ BasedCategory.ofFunctor (Functor.completion F.p)) :
    (homEquivInverse F G).obj ψ =
      BasedFunctor.comp (RestrictInclusion.map ψ) (completionCounit F) := rfl
/-- Restriction followed by evaluation is a quasi-inverse of the completion hom-functor. -/
theorem homEquivInverse_isQuasiInverse :
    Nonempty (Functor.id _ ≅ homEquivFunctor F G ⋙ homEquivInverse F G) ∧
      Nonempty (homEquivInverse F G ⋙ homEquivFunctor F G ≅ Functor.id _) := sorry
/-- The completion hom-functor is an equivalence of categories. -/
instance homEquivFunctor.isEquivalence : (homEquivFunctor F G).IsEquivalence := by
  rcases homEquivInverse_isQuasiInverse F G with ⟨⟨e₁⟩, ⟨e₂⟩⟩
  exact Functor.IsEquivalence.mk' (homEquivInverse F G) e₁ e₂
end CategoryTheory.CofiberedCategoryOver.Groupoids
end
