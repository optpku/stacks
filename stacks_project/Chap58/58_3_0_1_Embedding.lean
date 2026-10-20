module

public import ReasLib.CategoryTheory.Functor.AutEmbedding

@[expose] public section

universe u v w z

namespace CategoryTheory

namespace Functor

variable {C : Type u} [Category.{v} C] {D : Type w} [Category.{z} D] (F : C ⥤ D)

variable (σ τ : Aut F) (X : C)

#check (CategoryTheory.Functor.autEmbedding_map_mul F σ τ :
  (fun X : C ↦ (σ * τ).app X) = (fun X : C ↦ (τ.app X).trans (σ.app X)))

#check (CategoryTheory.Functor.autEmbedding F : Aut F →* ∀ X : C, Aut (F.obj X))

#check (CategoryTheory.Functor.autEmbedding_apply F σ X :
  CategoryTheory.Functor.autEmbedding F σ X = σ.app X)

#check (CategoryTheory.Functor.autEmbedding_injective F :
  Function.Injective (CategoryTheory.Functor.autEmbedding F))

end Functor

end CategoryTheory
