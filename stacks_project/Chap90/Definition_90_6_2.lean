module

public import Mathlib.CategoryTheory.FiberedCategory.BasedCategory
public import ReasLib.AlgebraicGeometry.FormalDeformation.Predeformation
import StacksCheckRecall

/-!
# Predeformation categories

A predeformation category is a category cofibered in groupoids over `C_Λ` whose
fibre over `k` is equivalent to a point. Morphisms are morphisms of categories
over `ArtinianLocalAlgCat Λ k`.
-/

@[expose] public section

open CategoryTheory

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{w} F]

variable (p : F ⥤ ArtinianLocalAlgCat Λ k)

/- Definition 90.6.2 (1): a predeformation category is a category cofibered in groupoids
over `ArtinianLocalAlgCat Λ k` whose fibre over `k` is equivalent to a category with a
single object and a single morphism. -/
@[stacks 06GS]
#check (CategoryTheory.Functor.IsPredeformationCategory p : Prop)

variable {G : Type v} [Category.{w} G]
variable (q : G ⥤ ArtinianLocalAlgCat Λ k)
variable [Functor.IsPredeformationCategory p] [Functor.IsPredeformationCategory q]

/- Definition 90.6.2 (2): a morphism of predeformation categories is a morphism of
categories cofibered in groupoids over `ArtinianLocalAlgCat Λ k`. -/
@[stacks 06GS]
#check (CategoryTheory.Functor.PredeformationMorphism p q : Type (max v w))
