module

public import ReasLib.AlgebraicGeometry.FormalDeformation.TypesCompletion.Morphism

/-!
# Completion of natural transformations

The completed morphism, identity, and composition APIs are available through the
shared mathematical owner.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

#check (CategoryTheory.Functor.typesCompletionMap :
  ∀ {F G : ArtinianLocalAlgCat Λ k ⥤ Type w}, (F ⟶ G) →
    (Functor.typesCompletion F ⟶ Functor.typesCompletion G))

#check (CategoryTheory.Functor.typesCompletionMap_id :
  ∀ (F : ArtinianLocalAlgCat Λ k ⥤ Type w),
    Functor.typesCompletionMap (𝟙 F) = 𝟙 (Functor.typesCompletion F))

#check (CategoryTheory.Functor.typesCompletionMap_comp :
  ∀ {F G H : ArtinianLocalAlgCat Λ k ⥤ Type w} (α : F ⟶ G) (β : G ⟶ H),
    Functor.typesCompletionMap (α ≫ β) =
      Functor.typesCompletionMap α ≫ Functor.typesCompletionMap β)
