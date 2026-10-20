module

public import Mathlib.CategoryTheory.EssentialImage
public import ReasLib.AlgebraicGeometry.FormalDeformation.Smooth
public import ReasLib.CategoryTheory.Cofibered.InGroupoids

/-!
# Functorial properties of smooth morphisms of cofibered groupoids

Smooth morphisms of categories cofibered in groupoids over
`ArtinianLocalAlgCat Λ k` are closed under composition, cancel on the left of
an essentially surjective morphism, and are stable under 2-fibre-product
base change.
-/

@[expose] public section

open CategoryTheory
open CofiberedCategoryOver.Groupoids
open scoped BasedFunctor Bicategory

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CategoryTheory.BasedFunctor

/-- The composite of two smooth morphisms of categories cofibered in groupoids over
`ArtinianLocalAlgCat Λ k` is smooth. -/
@[stacks 06HM]
instance instIsSmooth_comp {X Y Z : BasedCategory.{v, w} (ArtinianLocalAlgCat Λ k)}
    [Functor.IsFibered.InGroupoids X.p.op] [Functor.IsFibered.InGroupoids Y.p.op]
    [Functor.IsFibered.InGroupoids Z.p.op] (φ : X ⥤ᵇ Y) (ψ : Y ⥤ᵇ Z)
    [IsSmooth φ] [IsSmooth ψ] : IsSmooth (φ ⋙ ψ) := sorry

/-- If a morphism of categories cofibered in groupoids becomes smooth after precomposition
with an essentially surjective morphism, then it is smooth. -/
@[stacks 06HM]
theorem isSmooth_of_comp_essSurj {X Y Z : BasedCategory.{v, w} (ArtinianLocalAlgCat Λ k)}
    [Functor.IsFibered.InGroupoids X.p.op] [Functor.IsFibered.InGroupoids Y.p.op]
    [Functor.IsFibered.InGroupoids Z.p.op] (φ : X ⥤ᵇ Y) (ψ : Y ⥤ᵇ Z)
    [φ.toFunctor.EssSurj] [IsSmooth (φ ⋙ ψ)] : IsSmooth ψ := sorry

/-- The second projection of the 2-fibre product of a smooth morphism of categories cofibered
in groupoids over `ArtinianLocalAlgCat Λ k` with any morphism is smooth. -/
@[stacks 06HM]
instance instIsSmooth_twoFibreProduct_snd
    {F G G' : CofiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u}
      (ArtinianLocalAlgCat Λ k)}
    (φ : F ⟶ G) (τ : G' ⟶ G) [IsSmooth (toBasedFunctor φ)] :
    IsSmooth (toBasedFunctor (TwoFibreProduct.snd.{u + 1, u, u + 1, u} φ τ)) :=
    sorry

end CategoryTheory.BasedFunctor
