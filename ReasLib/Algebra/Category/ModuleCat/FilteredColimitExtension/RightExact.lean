module

public import ReasLib.Algebra.Category.ModuleCat.FilteredColimitExtension.Additive
public import Mathlib.CategoryTheory.Limits.ExactFunctor

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty

universe u v w z

namespace ModuleCat

/-- A right-exact functor on finitely presented `A`-modules has an additive
filtered-colimit-preserving extension to all `A`-modules. -/
theorem filteredColimitExtension_of_rightExact_additive
    {A : Type u} [Ring A] {B : Type w} [Category.{z} B]
    [Preadditive B] [HasFiniteBiproducts B] [HasCokernels B]
    [HasFilteredColimitsOfSize.{max u v, max u v} B]
    (F : (isFinitePresentation.{u, max u v} A).FullSubcategory ⥤ B)
    [PreservesFiniteColimits F]
    (F' : ModuleCat.{max u v} A ⥤ B)
    [PreservesFilteredColimitsOfSize.{max u v, max u v} F']
    (eF' : (isFinitePresentation.{u, max u v} A).ι ⋙ F' ≅ F) :
    F'.Additive := sorry

/-- A filtered-colimit-preserving extension of a right-exact functor on finitely presented
`A`-modules preserves finite colimits. -/
theorem filteredColimitExtension_of_rightExact_preservesFiniteColimits
    {A : Type u} [Ring A] {B : Type w} [Category.{z} B]
    [Preadditive B] [HasFiniteBiproducts B] [HasCokernels B]
    [HasFilteredColimitsOfSize.{max u v, max u v} B]
    (F : (isFinitePresentation.{u, max u v} A).FullSubcategory ⥤ B)
    [PreservesFiniteColimits F]
    (F' : ModuleCat.{max u v} A ⥤ B)
    [PreservesFilteredColimitsOfSize.{max u v, max u v} F']
    (eF' : (isFinitePresentation.{u, max u v} A).ι ⋙ F' ≅ F) :
    PreservesFiniteColimits F' := sorry

/-- A filtered-colimit-preserving extension of a right-exact functor on finitely presented
`A`-modules preserves coproducts indexed by types in the module universe. -/
theorem filteredColimitExtension_of_rightExact_preservesCoproducts
    {A : Type u} [Ring A] {B : Type w} [Category.{z} B]
    [Preadditive B] [HasFiniteBiproducts B] [HasCokernels B]
    [HasFilteredColimitsOfSize.{max u v, max u v} B]
    (F : (isFinitePresentation.{u, max u v} A).FullSubcategory ⥤ B)
    [PreservesFiniteColimits F]
    (F' : ModuleCat.{max u v} A ⥤ B)
    [PreservesFilteredColimitsOfSize.{max u v, max u v} F']
    (eF' : (isFinitePresentation.{u, max u v} A).ι ⋙ F' ≅ F)
    (J : Type (max u v)) :
    PreservesColimitsOfShape (Discrete J) F' := sorry

/-- A right-exact functor between finitely presented module categories has an extension
that preserves finite colimits under the corresponding restriction and filtered-colimit
preservation data. -/
theorem fpFilteredColimitExtension_preservesFiniteColimits
    {A : Type u} [Ring A] {B : Type v} [Ring B]
    (F : (isFinitePresentation.{u, max u v} A).FullSubcategory ⥤
      (isFinitePresentation.{v, max u v} B).FullSubcategory)
    [PreservesFiniteColimits F]
    (F' : ModuleCat.{max u v} A ⥤ ModuleCat.{max u v} B)
    (e : (isFinitePresentation.{u, max u v} A).ι ⋙ F' ≅
      F ⋙ (isFinitePresentation.{v, max u v} B).ι)
    [PreservesFilteredColimitsOfSize.{max u v, max u v} F'] :
    PreservesFiniteColimits F' := sorry

end ModuleCat
