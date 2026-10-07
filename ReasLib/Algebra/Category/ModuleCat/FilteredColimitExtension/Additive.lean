module

public import ReasLib.Algebra.Category.ModuleCat.FinitePresentation
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty

universe u v w z

namespace ModuleCat

/-- An extension of an additive functor from finitely presented `A`-modules that preserves
the specified filtered colimits is additive. -/
theorem filteredColimitExtension_additive
    {A : Type u} [Ring A] {B : Type w} [Category.{z} B]
    [Preadditive B] [HasFiniteBiproducts B]
    [HasFilteredColimitsOfSize.{max u v, max u v} B]
    (F : (isFinitePresentation.{u, max u v} A).FullSubcategory ⥤ B) [F.Additive]
    (F' : ModuleCat.{max u v} A ⥤ B)
    [PreservesFilteredColimitsOfSize.{max u v, max u v} F']
    (eF' : (isFinitePresentation.{u, max u v} A).ι ⋙ F' ≅ F) :
    F'.Additive := sorry

/-- An extension of an additive functor from finitely presented `A`-modules that preserves
the specified filtered colimits preserves arbitrary coproducts indexed by a type in the fixed
universe of modules. -/
theorem filteredColimitExtension_preservesCoproducts
    {A : Type u} [Ring A] {B : Type w} [Category.{z} B]
    [Preadditive B] [HasFiniteBiproducts B]
    [HasFilteredColimitsOfSize.{max u v, max u v} B]
    (F : (isFinitePresentation.{u, max u v} A).FullSubcategory ⥤ B) [F.Additive]
    (F' : ModuleCat.{max u v} A ⥤ B)
    [PreservesFilteredColimitsOfSize.{max u v, max u v} F']
    (eF' : (isFinitePresentation.{u, max u v} A).ι ⋙ F' ≅ F)
    (J : Type (max u v)) :
    PreservesColimitsOfShape (Discrete J) F' := sorry

/-- An additive functor between finitely presented module categories has an additive
filtered-colimit-preserving extension to all modules under the corresponding restriction
isomorphism and filtered-colimit preservation data. -/
theorem fpFilteredColimitExtension_additive
    {A : Type u} [Ring A] {B : Type v} [Ring B]
    (F : (isFinitePresentation.{u, max u v} A).FullSubcategory ⥤
      (isFinitePresentation.{v, max u v} B).FullSubcategory) [F.Additive]
    (F' : ModuleCat.{max u v} A ⥤ ModuleCat.{max u v} B)
    (e : (isFinitePresentation.{u, max u v} A).ι ⋙ F' ≅
      F ⋙ (isFinitePresentation.{v, max u v} B).ι)
    [PreservesFilteredColimitsOfSize.{max u v, max u v} F'] :
    F'.Additive := sorry

/-- An additive filtered-colimit-preserving extension between module categories preserves
coproducts indexed by any type in the module universe. -/
theorem fpFilteredColimitExtension_preservesCoproducts
    {A : Type u} [Ring A] {B : Type v} [Ring B]
    (F : (isFinitePresentation.{u, max u v} A).FullSubcategory ⥤
      (isFinitePresentation.{v, max u v} B).FullSubcategory) [F.Additive]
    (F' : ModuleCat.{max u v} A ⥤ ModuleCat.{max u v} B)
    (e : (isFinitePresentation.{u, max u v} A).ι ⋙ F' ≅
      F ⋙ (isFinitePresentation.{v, max u v} B).ι)
    [PreservesFilteredColimitsOfSize.{max u v, max u v} F']
    (J : Type (max u v)) :
    PreservesColimitsOfShape (Discrete J) F' := sorry

end ModuleCat
