module

import StacksCheckRecall
public import stacks_project.Chap96.«96_7_1_1_Comparison»
public import stacks_project.Chap96.«96_7_1_1_InverseImage»
public import stacks_project.Chap96.«96_7_1_1_Pushforward»

@[expose] public section

open AlgebraicGeometry CategoryTheory FiberedCategoryOver.Groupoids
open AlgebraicGeometry.GroupoidsOver
open scoped Bicategory

universe u z

variable {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y)

/- 96.7.1.1 (1): a 1-morphism `f : X ⟶ Y` of categories fibred in groupoids over
`(Sch/S)_fppf` induces the inverse image `f⁻¹ : PMod(𝒪_Y) ⥤ PMod(𝒪_X)` by
precomposition, using `𝒪_Y(f(x)) = 𝒪_X(x)`. -/
@[stacks 06WD] #check
  (presheafModuleInverseImage f :
    PresheafOfModules.{z} (structureSheaf Y).obj ⥤
      PresheafOfModules.{z} (structureSheaf X).obj)

variable [∀ P : X.totalᵒᵖ ⥤ Type u, (toFunctor f).op.HasPointwiseRightKanExtension P]

/- 96.7.1.1 (2): the matching direct image `f_* : PMod(𝒪_X) ⥤ PMod(𝒪_Y)`, obtained
by viewing `X` and `Y` as chaotic sites and taking the module pushforward of the
associated morphism of ringed topoi. -/
@[stacks 06WD] #check
  (presheafModulePushforward f :
    PresheafOfModules.{u} (structureSheaf X).obj ⥤
      PresheafOfModules.{u} (structureSheaf Y).obj)
