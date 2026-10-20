module

public import Mathlib.CategoryTheory.FiberedCategory.BasedCategory
public import ReasLib.AlgebraicGeometry.FormalDeformation.DeformationCategory
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

variable {G : Type v} [Category.{w} G]
variable (p : F ⥤ ArtinianLocalAlgCat Λ k) (q : G ⥤ ArtinianLocalAlgCat Λ k)

/- Definition 90.16.8: a deformation category is a predeformation category
satisfying (RS), and a morphism of deformation categories is a morphism of
categories over `ArtinianLocalAlgCat Λ k`. -/
@[stacks 06J9] #check (CategoryTheory.Functor.IsDeformationCategory p : Prop)

variable [Functor.IsDeformationCategory p] [Functor.IsDeformationCategory q]

/- Morphisms of deformation categories are morphisms of categories over
`ArtinianLocalAlgCat Λ k`. -/
#check (CategoryTheory.BasedFunctor
  (CategoryTheory.BasedCategory.ofFunctor p) (CategoryTheory.BasedCategory.ofFunctor q) :
  Type (max v w))
