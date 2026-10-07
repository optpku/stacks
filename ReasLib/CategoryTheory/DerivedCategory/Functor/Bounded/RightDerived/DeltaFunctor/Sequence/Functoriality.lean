module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.DeltaFunctor.Sequence.Naturality
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Functorial Right-Derived Exact Windows

For a fixed bounded-below right-derived model and degree, direct `RⁿF` exact
windows form a functor on the category of short exact complexes.
-/

open CategoryTheory.ComposableArrows
open scoped CategoryTheory

noncomputable section

universe w vA vB uA uB

namespace CategoryTheory.Functor.RightDerived.cohomological.exactWindow

variable {A : Type uA} {B : Type uB}
  [Category.{vA} A] [Category.{vB} B]
  [Abelian A] [Abelian B]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
  (RF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B)
  [RF.CommShift ℤ] [RF.IsTriangulated]

/-- Identity morphisms in the short-exact full subcategory induce identity
maps of direct right-derived exact windows. -/
theorem map_id_hom (n : ℕ)
    (S : (ShortComplex.shortExact A).FullSubcategory) :
    map RF S.property S.property (InducedCategory.Hom.hom (𝟙 S)) n =
      𝟙 (RightDerived.cohomological.exactWindow RF S.property n) := sorry

/-- Composition in the short-exact full subcategory is preserved by direct
right-derived exact-window maps. -/
theorem map_comp_hom (n : ℕ)
    {S T U : (ShortComplex.shortExact A).FullSubcategory}
    (φ : S ⟶ T) (ψ : T ⟶ U) :
    map RF S.property U.property (φ ≫ ψ).hom n =
      map RF S.property T.property φ.hom n ≫
        map RF T.property U.property ψ.hom n := sorry

/-- At a fixed degree, direct right-derived exact windows are functorial in
the short exact complex. -/
@[stacks 05TE "functor of right-derived exact windows"]
noncomputable def functor
    (RF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B)
    [RF.CommShift ℤ] [RF.IsTriangulated] (n : ℕ) :
    (ShortComplex.shortExact A).FullSubcategory ⥤ ComposableArrows B 5 where
  obj S := RightDerived.cohomological.exactWindow RF S.property n
  map := fun {S T} φ ↦ map RF S.property T.property φ.hom n
  map_id := map_id_hom RF n
  map_comp := map_comp_hom RF n

/-- The object value of the direct right-derived exact-window functor is the
corresponding explicit window. -/
@[simp]
theorem functor_obj (n : ℕ)
    (S : (ShortComplex.shortExact A).FullSubcategory) :
    (functor RF n).obj S =
      RightDerived.cohomological.exactWindow RF S.property n := sorry

/-- The map of the direct right-derived exact-window functor is its pointwise
naturality map. -/
@[simp]
theorem functor_map (n : ℕ)
    {S T : (ShortComplex.shortExact A).FullSubcategory} (φ : S ⟶ T) :
    (functor RF n).map φ = map RF S.property T.property φ.hom n := sorry

/-- The functor of low-degree right-derived exact windows. -/
abbrev lowDegreeFunctor
    (RF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B)
    [RF.CommShift ℤ] [RF.IsTriangulated] :
    (ShortComplex.shortExact A).FullSubcategory ⥤ ComposableArrows B 5 :=
  functor RF 0

end CategoryTheory.Functor.RightDerived.cohomological.exactWindow
