module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.DeltaFunctor.Sequence.Augmented.Naturality
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.DeltaFunctor.Sequence.Functoriality
public import ReasLib.CategoryTheory.ComposableArrows.ZeroPrecomp.Functor
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Functorial Augmented Right-Derived Windows

For a fixed bounded-below right-derived model, standard low-degree sequences
form a functor on the category of short exact complexes.
-/

open CategoryTheory.ComposableArrows
open scoped CategoryTheory

noncomputable section

universe w vA vB uA uB

namespace CategoryTheory.Functor.RightDerived.cohomological.augmentedWindow

variable {A : Type uA} {B : Type uB}
  [Category.{vA} A] [Category.{vB} B]
  [Abelian A] [Abelian B]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]

/-- Direct augmented right-derived windows are functorial in the short exact
complex. -/
@[stacks 05TE "functor of augmented right-derived windows"]
noncomputable def functor
    (RF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B)
    [RF.CommShift ℤ] [RF.IsTriangulated] :
    (ShortComplex.shortExact A).FullSubcategory ⥤ ComposableArrows B 6 :=
  exactWindow.functor RF 0 ⋙ zeroPrecomp.functor 1

variable (RF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B)
  [RF.CommShift ℤ] [RF.IsTriangulated]

/-- The object action of the direct augmented-window functor is the explicit
augmented sequence. -/
@[simp]
theorem functor_obj (S : (ShortComplex.shortExact A).FullSubcategory) :
    (functor RF).obj S =
      RightDerived.cohomological.augmentedWindow RF S.property := sorry

/-- The morphism action of the direct augmented-window functor is its
pointwise naturality map. -/
@[simp]
theorem functor_map {S T : (ShortComplex.shortExact A).FullSubcategory}
    (φ : S ⟶ T) :
    (functor RF).map φ = map RF S.property T.property φ.hom := sorry

/-- Forgetting the initial zero component of the direct augmented-window
functor recovers the low-degree exact-window functor. -/
@[simp]
theorem functor_comp_δ₀ :
    functor RF ⋙ δ₀Functor = exactWindow.functor RF 0 := sorry

end CategoryTheory.Functor.RightDerived.cohomological.augmentedWindow
