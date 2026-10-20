module

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.Operations

/-!
# Schemes of finite presentation over a base

This leaf owns the full subcategory of the slice `Over T` consisting of
finite-presentation morphisms to `T`. It uses the generic
`MorphismProperty.overObj` construction, and packages its stability under
base change as a functor between those slice subcategories.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

/-- The object property on `Over T` induced by finite-presentation scheme morphisms. -/
abbrev finitePresentationOverProperty (T : Scheme.{u}) : ObjectProperty (Over T) :=
  MorphismProperty.overObj @Scheme.Hom.FinitePresentation

/-- The full subcategory of schemes of finite presentation over a base scheme `T`. -/
abbrev FinitePresentationOver (T : Scheme.{u}) : Type (u + 1) :=
  (finitePresentationOverProperty T).FullSubcategory

namespace FinitePresentationOver

/-- The inclusion of schemes of finite presentation over `T` into all schemes over `T`. -/
abbrev inclusion (T : Scheme.{u}) : FinitePresentationOver T ⥤ Over T :=
  (finitePresentationOverProperty T).ι

/-- The structure morphism of an object of `FinitePresentationOver T` is of finite
presentation. -/
instance instFinitePresentationHom {T : Scheme.{u}} (X : FinitePresentationOver T) :
    Scheme.Hom.FinitePresentation X.obj.hom := sorry

/-- Base change preserves the finite-presentation-over property. -/
theorem baseChange_mem {T T' : Scheme.{u}} (f : T' ⟶ T)
    (X : FinitePresentationOver T) :
    finitePresentationOverProperty T' ((Over.pullback f).obj X.obj) := sorry

/-- The base-change functor on finite-presentation over-categories. -/
abbrev baseChange {T T' : Scheme.{u}} (f : T' ⟶ T) :
    FinitePresentationOver T ⥤ FinitePresentationOver T' :=
  ObjectProperty.lift (finitePresentationOverProperty T')
    ((inclusion T) ⋙ Over.pullback f) (fun X ↦ baseChange_mem f X)

end FinitePresentationOver

end AlgebraicGeometry
