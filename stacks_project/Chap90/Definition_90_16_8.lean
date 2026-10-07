module

public import Mathlib.CategoryTheory.FiberedCategory.BasedCategory
public import stacks_project.Chap90.Definition_90_16_8_Predeformation
public import stacks_project.Chap90.Definition_90_16_8_RimSchlessinger
import StacksCheckRecall

/-!
# Deformation categories

A deformation category is a predeformation category satisfying the Rim-Schlessinger
condition (RS). Morphisms of deformation categories are morphisms of categories over
`ArtinianLocalAlgCat Λ k`.
-/

@[expose] public section

open CategoryTheory

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{w} F]

namespace CategoryTheory.Functor

/-- Definition 90.16.8 (1): a deformation category is a predeformation category
satisfying (RS). -/
@[stacks 06J9]
class IsDeformationCategory (p : F ⥤ ArtinianLocalAlgCat Λ k) : Prop
    extends IsPredeformationCategory p where
  [hasRimSchlessinger : HasRimSchlessinger p]

/-- The identity functor on `ArtinianLocalAlgCat Λ k` is a deformation category. -/
instance instIsDeformationCategoryId :
    IsDeformationCategory (𝟭 (ArtinianLocalAlgCat Λ k)) := sorry

/-- A functor is a deformation category iff it is a predeformation category and satisfies
the Rim-Schlessinger condition (RS). -/
theorem isDeformationCategory_iff (p : F ⥤ ArtinianLocalAlgCat Λ k) :
    IsDeformationCategory p ↔ IsPredeformationCategory p ∧ HasRimSchlessinger p := sorry

end CategoryTheory.Functor

variable {G : Type v} [Category.{w} G]
variable (p : F ⥤ ArtinianLocalAlgCat Λ k) (q : G ⥤ ArtinianLocalAlgCat Λ k)
variable [Functor.IsDeformationCategory p] [Functor.IsDeformationCategory q]

/- Definition 90.16.8 (2): a morphism of deformation categories is a morphism of
categories over `ArtinianLocalAlgCat Λ k`. -/
@[stacks 06J9]
#check (BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor q)
