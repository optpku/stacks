module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Smooth.TangentCriterion
import StacksCheckRecall

/-!
# Smoothness of a map of deformation categories

A morphism of deformation categories is smooth if and only if its differential on
tangent spaces is surjective and lifts along small extensions exist whenever they
exist for the image object.
-/

open CategoryTheory
open scoped Bicategory

universe u v w

/- Lemma 90.20.3: A morphism of deformation categories is smooth if and only if
its tangent differential is surjective and objects lift along small extensions
whenever their images lift. -/
@[stacks 0DYP] #check
  (CategoryTheory.BasedFunctor.isSmooth_iff_surjective_differential :
    ∀ {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
      [Module.Finite Λ k]
      {F G : Type v} [Category.{w} F] [Category.{w} G]
      {p : F ⥤ ArtinianLocalAlgCat Λ k} {q : G ⥤ ArtinianLocalAlgCat Λ k}
      [Functor.IsDeformationCategory p] [Functor.IsDeformationCategory q]
      (φ : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor q),
      CategoryTheory.BasedFunctor.IsSmooth φ ↔
        Function.Surjective (CategoryTheory.BasedFunctor.differential φ) ∧
          CategoryTheory.BasedFunctor.existsLiftOfImageLift φ)
