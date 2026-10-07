module

public import stacks_project.Chap90.Remark_90_7_9_Unit

/-!
# Hom-category equivalence of completion and restriction

For `F` over `C_Λ` and `G` over `Ĉ_Λ`, the functor
`Φ : Mor_{C_Λ}(G|_{C_Λ}, F) ⥤ Mor_{Ĉ_Λ}(G, hat F)` sends `φ` to the composite of the
unit with the induced map of formal objects, and has quasi-inverse `Ψ` sending `ψ` to
the restriction of `ψ` postcomposed with the counit.
-/

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

/-- Apply a based functor `φ : G|_{C_Λ} ⥤ᵇ F` stagewise to formal objects of the
Hom-universe lift of the restriction. -/
def completionMap (φ : (restrictInclusion G).toBasedCategory ⥤ᵇ F.toBasedCategory) :
    BasedCategory.ofFunctor
        (Functor.completion (RestrictInclusion.projectionTotal G.toBasedCategory)) ⥤ᵇ
      BasedCategory.ofFunctor (Functor.completion F.p) where
  toFunctor :=
    { obj ξ :=
        FormalObject.of ξ.base
          (fun n ↦ φ.obj (ULiftHom.objDown (ξ.system.family n)))
          (fun n ↦ φ.map (ULiftHom.down.map (ξ.system.stepMap n)))
          (fun n ↦ sorry) (fun n ↦ sorry)
      map a :=
        { base := a.base
          app := fun n ↦ φ.map (ULiftHom.down.map (a.app n))
          baseTrunc := a.baseTrunc
          over := sorry
          baseTrunc_spec := a.baseTrunc_spec
          naturality := sorry }
      map_id := sorry
      map_comp := sorry }
  w := sorry

/-- A based `2`-morphism over `C_Λ` induces a based `2`-morphism of completions of the
restriction. -/
def completionMap₂ {φ ψ : (restrictInclusion G).toBasedCategory ⥤ᵇ F.toBasedCategory}
    (t : φ ⟶ ψ) : completionMap F G φ ⟶ completionMap F G ψ where
  toNatTrans :=
    { app ξ :=
        { base := 𝟙 ξ.base
          app := fun n ↦ t.toNatTrans.app (ULiftHom.objDown (ξ.system.family n))
          baseTrunc := fun n ↦ 𝟙 (ξ.base.truncation n)
          over := sorry
          baseTrunc_spec := sorry
          naturality := sorry }
      naturality := sorry }
  isHomLift' := sorry

/-- The functor `Φ` sending a morphism `φ : G|_{C_Λ} ⟶ F` over `C_Λ` to
`G ⟶ hat(G|_{C_Λ}) ⟶ hat F`. -/
def homEquivFunctor :
    ((restrictInclusion G).toBasedCategory ⥤ᵇ F.toBasedCategory) ⥤
      (G.toBasedCategory ⥤ᵇ BasedCategory.ofFunctor (Functor.completion F.p)) where
  obj φ := BasedFunctor.comp (completionUnit G) (completionMap F G φ)
  map t := BasedCategory.whiskerLeft (completionUnit G) (completionMap₂ F G t)
  map_id := sorry
  map_comp := sorry

/-- `Φ` sends `φ` to the composite of the unit with the induced map of formal objects. -/
theorem homEquivFunctor_obj
    (φ : (restrictInclusion G).toBasedCategory ⥤ᵇ F.toBasedCategory) :
    (homEquivFunctor F G).obj φ =
      BasedFunctor.comp (completionUnit G) (completionMap F G φ) := sorry

/-- The quasi-inverse `Ψ` sending a morphism `ψ : G ⟶ hat F` over `Ĉ_Λ` to
`G|_{C_Λ} ⟶ hat F |_{C_Λ} ⟶ F`. -/
def homEquivInverse :
    (G.toBasedCategory ⥤ᵇ BasedCategory.ofFunctor (Functor.completion F.p)) ⥤
      ((restrictInclusion G).toBasedCategory ⥤ᵇ F.toBasedCategory) where
  obj ψ := BasedFunctor.comp (RestrictInclusion.map ψ) (completionCounit F)
  map t := BasedCategory.whiskerRight (RestrictInclusion.map₂ t) (completionCounit F)
  map_id := sorry
  map_comp := sorry

/-- `Ψ` sends `ψ` to the composite of the restricted map with the counit. -/
theorem homEquivInverse_obj
    (ψ : G.toBasedCategory ⥤ᵇ BasedCategory.ofFunctor (Functor.completion F.p)) :
    (homEquivInverse F G).obj ψ =
      BasedFunctor.comp (RestrictInclusion.map ψ) (completionCounit F) := sorry

/-- `Φ` is an equivalence of hom-categories. -/
instance homEquivFunctor.isEquivalence : (homEquivFunctor F G).IsEquivalence := sorry

end CategoryTheory.CofiberedCategoryOver.Groupoids

end
