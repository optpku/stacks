/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.EssentialImage
public import stacks_project.Chap90.Definition_90_8_1_Smooth
public import stacks_project.Chap90.Remarks_90_5_2_Groupoids

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

/-- Lemma 90.8.7 (1): if `φ : X ⥤ᵇ Y` and `ψ : Y ⥤ᵇ Z` are smooth morphisms of
categories cofibered in groupoids over `ArtinianLocalAlgCat Λ k`, then the
composite `φ ⋙ ψ` (source `ψ ∘ φ`) is smooth. -/
@[stacks 06HM]
instance instIsSmooth_comp {X Y Z : BasedCategory.{v, w} (ArtinianLocalAlgCat Λ k)}
    [Functor.IsFibered.InGroupoids X.p.op] [Functor.IsFibered.InGroupoids Y.p.op]
    [Functor.IsFibered.InGroupoids Z.p.op] (φ : X ⥤ᵇ Y) (ψ : Y ⥤ᵇ Z)
    [IsSmooth φ] [IsSmooth ψ] : IsSmooth (φ ⋙ ψ) := sorry

/-- Lemma 90.8.7 (2): if `φ : X ⥤ᵇ Y` is essentially surjective and the composite
`φ ⋙ ψ` is smooth, then `ψ` is smooth. -/
@[stacks 06HM]
theorem isSmooth_of_comp_essSurj {X Y Z : BasedCategory.{v, w} (ArtinianLocalAlgCat Λ k)}
    [Functor.IsFibered.InGroupoids X.p.op] [Functor.IsFibered.InGroupoids Y.p.op]
    [Functor.IsFibered.InGroupoids Z.p.op] (φ : X ⥤ᵇ Y) (ψ : Y ⥤ᵇ Z)
    [φ.toFunctor.EssSurj] [IsSmooth (φ ⋙ ψ)] : IsSmooth ψ := sorry

/-- Lemma 90.8.7 (3): if `φ : F ⟶ G` is a smooth morphism of categories cofibered
in groupoids over `ArtinianLocalAlgCat Λ k` and `τ : G' ⟶ G` is any such
morphism, then the 2-fibre-product projection
`toBasedFunctor (TwoFibreProduct.snd φ τ)` (`F ×_G G' ⟶ G'`, definitionally
`PseudoPullback.snd` of the underlying based functors) is smooth. -/
@[stacks 06HM]
instance instIsSmooth_twoFibreProduct_snd
    {F G G' : CofiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u}
      (ArtinianLocalAlgCat Λ k)}
    (φ : F ⟶ G) (τ : G' ⟶ G) [IsSmooth (toBasedFunctor φ)] :
    IsSmooth (toBasedFunctor (TwoFibreProduct.snd.{u + 1, u, u + 1, u} φ τ)) :=
    sorry

end CategoryTheory.BasedFunctor
