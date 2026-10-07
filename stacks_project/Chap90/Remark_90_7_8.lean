module

public import ReasLib.CategoryTheory.Bicategory.FullSubbicategory.Lift.Construction
public import stacks_project.Chap90.Definition_90_7_3
public import stacks_project.Chap90.Remark_90_7_8_Groupoids
public import stacks_project.Chap90.Remark_90_7_8_Map

/-!
# Completion as a 2-functor on categories cofibered in groupoids

A morphism of categories cofibered in groupoids over `C_Λ` induces a morphism of
completions over `Ĉ_Λ` by applying it stagewise to formal objects, and a `2`-morphism
likewise induces a `2`-morphism of completions. These assemble into a strict
`2`-functor on `CofiberedCategoryOver.Groupoids`.
-/

@[expose] public section

open CategoryTheory CofiberedCategoryOver.Groupoids ObjectProperty
open scoped BasedFunctor Bicategory

universe u v

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CategoryTheory.Functor

/-- Remark 90.7.8: a 1-morphism `φ : F ⟶ G` of categories cofibered in groupoids over
`ArtinianLocalAlgCat Λ k` induces a 1-morphism of completions over
`CompleteLocalAlgCat Λ k` by sending a formal object `(R, ξ_n, f_n)` to
`(R, φ.obj ξ_n, φ.map f_n)` and a morphism `(a_0, a_n)` to `(a_0, φ.map a_n)`. A
2-morphism `t : φ ⟶ φ'` induces a 2-morphism of completions whose component at a
formal object `ξ` has identity base map and stage maps `t.app ξ_n`. These assemble
into a strict 2-functor
`CofiberedCategoryOver.Groupoids (ArtinianLocalAlgCat Λ k) ⥤
CofiberedCategoryOver.Groupoids (CompleteLocalAlgCat Λ k)`. -/
@[stacks 06H9]
noncomputable def completionStrictPseudofunctor :
    StrictPseudofunctor
      (CofiberedCategoryOver.Groupoids.{u + 1, u, v, v} (ArtinianLocalAlgCat Λ k))
      (CofiberedCategoryOver.Groupoids.{u + 1, u, max (u + 1) v, max u v}
        (CompleteLocalAlgCat Λ k)) :=
  FullSubbicategory.lift FormalObject.completionAmbient
    (fun X ↦ completion_op_isFiberedInGroupoids X.p)

/-- The completion 2-functor sends a category cofibered in groupoids to the completion
of its projection. -/
theorem completionStrictPseudofunctor_obj
    (X : CofiberedCategoryOver.Groupoids.{u + 1, u, v, v} (ArtinianLocalAlgCat Λ k)) :
    (completionStrictPseudofunctor.obj X).p = completion X.p := sorry

/-- The completion 2-functor sends a 1-morphism to the induced based functor of
formal objects. -/
theorem completionStrictPseudofunctor_map
    {X Y : CofiberedCategoryOver.Groupoids.{u + 1, u, v, v} (ArtinianLocalAlgCat Λ k)}
    (φ : X ⟶ Y) :
    toBasedFunctor (completionStrictPseudofunctor.map φ) =
      FormalObject.basedMap (toBasedFunctor φ) := sorry

/-- The completion 2-functor sends a 2-morphism to the induced based natural
transformation of formal objects. -/
theorem completionStrictPseudofunctor_map₂
    {X Y : CofiberedCategoryOver.Groupoids.{u + 1, u, v, v} (ArtinianLocalAlgCat Λ k)}
    {φ φ' : X ⟶ Y} (t : φ ⟶ φ') :
    toBasedNatTrans (completionStrictPseudofunctor.map₂ t) =
      FormalObject.basedMap₂ (toBasedNatTrans t) := sorry

end CategoryTheory.Functor
