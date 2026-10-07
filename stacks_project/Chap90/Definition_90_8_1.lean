module

public import stacks_project.Chap90.Definition_90_8_1_Smooth

/-!
# Smooth morphisms of categories cofibered in groupoids

A morphism of categories cofibered in groupoids over `C_Λ` is smooth when it
satisfies the infinitesimal lifting property along surjections.
-/

@[expose] public section

open CategoryTheory

universe u v w v' w'

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type w} [Category.{v} F]
variable {G : Type w'} [Category.{v'} G]

namespace CategoryTheory.BasedFunctor

/-- Definition 90.8.1: a morphism `φ` of categories cofibered in groupoids over
`ArtinianLocalAlgCat Λ k` is smooth if and only if for every surjection `f : B ⟶ A`
and every `α : y ⟶ φ.obj x` lying over `f`, there exist `x'` over `B`, a morphism
`x' ⟶ x` over `f`, and a morphism `φ.obj x' ⟶ y` over `𝟙 B` making the triangle
commute. -/
@[stacks 06HG]
theorem isSmooth_iff {p : F ⥤ ArtinianLocalAlgCat Λ k} {q : G ⥤ ArtinianLocalAlgCat Λ k}
    [Functor.IsFibered.InGroupoids p.op] [Functor.IsFibered.InGroupoids q.op]
    (φ : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor q) :
    IsSmooth φ ↔
      ∀ {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A), Function.Surjective f.hom →
        ∀ {y : G} {x : F} (α : y ⟶ φ.obj x), q.IsHomLift f α →
          ∃ (x' : F) (β : x' ⟶ x) (γ : φ.obj x' ⟶ y),
            p.IsHomLift f β ∧ q.IsHomLift (𝟙 B) γ ∧ γ ≫ α = φ.map β := sorry

end CategoryTheory.BasedFunctor
