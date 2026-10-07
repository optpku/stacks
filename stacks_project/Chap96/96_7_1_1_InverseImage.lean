module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import stacks_project.Chap96.«96_7_1_1_Comparison»

/-!
# Inverse image of presheaves of modules

A 1-morphism `f : X ⟶ Y` of categories fibred in groupoids induces
`f⁻¹ : PMod(𝒪_Y) ⥤ PMod(𝒪_X)` by precomposition of modules along
`toFunctor f`, using the identification `f⁻¹ 𝒪_Y = 𝒪_X`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Functor Opposite
open FiberedCategoryOver.Groupoids

noncomputable section

universe u z

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- Inverse image of presheaves of modules along a 1-morphism
`f : X ⟶ Y`, i.e. Stacks `f⁻¹ : PMod(𝒪_Y) ⥤ PMod(𝒪_X)`. -/
abbrev presheafModuleInverseImage {X Y : GroupoidsOver S} (f : X ⟶ Y) :
    PresheafOfModules.{z} (structureSheaf Y).obj ⥤
      PresheafOfModules.{z} (structureSheaf X).obj :=
  PresheafOfModules.pushforward.{z} (structureSheafInverseImageIso f).inv

/-- Inverse image of presheaves of modules commutes with the forgetful functor
to abelian presheaves, and is precomposition with `(toFunctor f).op`. -/
def presheafModuleInverseImage_toPresheaf {X Y : GroupoidsOver S} (f : X ⟶ Y) :
    presheafModuleInverseImage f ⋙
        PresheafOfModules.toPresheaf (structureSheaf X).obj ≅
      PresheafOfModules.toPresheaf (structureSheaf Y).obj ⋙
        (whiskeringLeft _ _ _).obj (toFunctor f).op :=
  PresheafOfModules.pushforwardCompToPresheaf (structureSheafInverseImageIso f).inv

/-- The inverse image of a presheaf of modules evaluates at `x` as the original
module at `f(x)`, with scalars restricted along `𝒪_Y(f(x)) = 𝒪_X(x)`. -/
theorem presheafModuleInverseImage_obj {X Y : GroupoidsOver S} (f : X ⟶ Y)
    (𝒢 : PresheafOfModules.{z} (structureSheaf Y).obj) (x : X.total) :
    ((presheafModuleInverseImage f).obj 𝒢).obj (op x) =
      (ModuleCat.restrictScalars
          ((structureSheafInverseImageIso f).inv.app (op x)).hom).obj
        ((PresheafOfModules.pushforward₀Obj (toFunctor f) (structureSheaf Y).obj 𝒢).obj
          (op x)) := sorry

end AlgebraicGeometry.GroupoidsOver
