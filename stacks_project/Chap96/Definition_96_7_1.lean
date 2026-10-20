module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Basic
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u z

/- Definition 96.7.1 (1): let `X` be a category fibred in groupoids over
`(Sch/S)_fppf`. A presheaf of modules on `X` is a presheaf of `𝒪_X`-modules.
The category of presheaves of modules is denoted `PMod(𝒪_X)`. -/
@[stacks 06WB] #check
  (AlgebraicGeometry.GroupoidsOver.PMod.{u, z} :
    {S : Scheme.{u}} → GroupoidsOver S → Type (max (u + 1) (z + 1)))

/- Definition 96.7.1 (2): a presheaf of modules `F` is an `𝒪_X`-module, or more
precisely a sheaf of `𝒪_X`-modules, if `F` is an fppf sheaf. The category of
`𝒪_X`-modules is denoted `Mod(𝒪_X)`. -/
@[stacks 06WB] #check
  (AlgebraicGeometry.GroupoidsOver.Mod.{u, z} :
    {S : Scheme.{u}} → GroupoidsOver S → Type (max (u + 1) (z + 1)))

variable {S : Scheme.{u}} (X : GroupoidsOver S)
variable (F G : PresheafOfModules.{z} (GroupoidsOver.structureSheaf X).obj)
variable (ℱ 𝒢 : SheafOfModules.{z} (GroupoidsOver.structureSheaf X))

/- Morphisms of presheaves of `𝒪_X`-modules are morphisms in
`PresheafOfModules (structureSheaf X).obj`. -/
#check (F ⟶ G)

/- Forgetting the module structure gives the underlying abelian presheaf. -/
#check (PresheafOfModules.toPresheaf.{z} (GroupoidsOver.structureSheaf X).obj)

/- Morphisms of sheaves of `𝒪_X`-modules are morphisms in
`SheafOfModules (structureSheaf X)`. -/
#check (ℱ ⟶ 𝒢)

/- The canonical forgetful functor remembers the underlying module presheaf. -/
#check (SheafOfModules.forget.{z} (GroupoidsOver.structureSheaf X))

/- The canonical forgetful functor remembers the underlying fppf sheaf of
abelian groups. -/
#check (SheafOfModules.toSheaf.{z} (GroupoidsOver.structureSheaf X))
