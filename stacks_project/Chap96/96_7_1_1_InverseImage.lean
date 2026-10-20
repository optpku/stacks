module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.PresheafModule

@[expose] public section

open AlgebraicGeometry CategoryTheory FiberedCategoryOver.Groupoids
open AlgebraicGeometry.GroupoidsOver
open scoped Bicategory

universe u z

variable {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y)

/- Inverse image of module presheaves by precomposition and canonical restriction of scalars. -/
#check (AlgebraicGeometry.GroupoidsOver.presheafModuleInverseImage f :
  PresheafOfModules.{z} (structureSheaf Y).obj ⥤
    PresheafOfModules.{z} (structureSheaf X).obj)
