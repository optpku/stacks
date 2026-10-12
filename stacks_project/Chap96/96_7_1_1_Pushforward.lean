/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Bottom
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.HomOfCocontinuous
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module
public import ReasLib.CategoryTheory.Sites.Chaotic
public import stacks_project.Chap96.«96_7_1_1_Comparison»

/-!
# Direct image of presheaves of modules

A 1-morphism `f : X ⟶ Y` of categories fibred in groupoids induces
`f_* : PMod(𝒪_X) ⥤ PMod(𝒪_Y)` by transporting the module pushforward of the
associated morphism of chaotic ringed topoi across the equivalence between
sheaves of modules and presheaves of modules on the bottom topology.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Functor Opposite
open FiberedCategoryOver.Groupoids

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- The underlying functor of sites of a 1-morphism, as a functor of chaotic
ringed sites. -/
abbrev chaoticToFunctor {X Y : GroupoidsOver S} (f : X ⟶ Y) :
    chaoticRingedSite X ⥤ chaoticRingedSite Y :=
  toFunctor f

/-- The morphism of chaotic ringed topoi associated to a 1-morphism of
categories fibred in groupoids. -/
def chaoticRingedToposHom {X Y : GroupoidsOver S} (f : X ⟶ Y)
    [∀ P : X.totalᵒᵖ ⥤ Type u, (toFunctor f).op.HasPointwiseRightKanExtension P] :
    RingedSite.ToposHom (chaoticRingedSite X) (chaoticRingedSite Y) :=
  RingedSite.Cocontinuous.toRingedTopos (chaoticToFunctor f)
    (structureSheafInverseImageIso f).hom

/-- Direct image of presheaves of modules along a 1-morphism
`f : X ⟶ Y`, i.e. Stacks `f_* : PMod(𝒪_X) ⥤ PMod(𝒪_Y)`. -/
abbrev presheafModulePushforward {X Y : GroupoidsOver S} (f : X ⟶ Y)
    [∀ P : X.totalᵒᵖ ⥤ Type u, (toFunctor f).op.HasPointwiseRightKanExtension P] :
    PresheafOfModules.{u} (structureSheaf X).obj ⥤
      PresheafOfModules.{u} (structureSheaf Y).obj :=
  (SheafOfModules.Bottom.equivalence (chaoticStructureSheaf X)).inverse ⋙
    (chaoticRingedToposHom f).modulePushforward ⋙
    (SheafOfModules.Bottom.equivalence (chaoticStructureSheaf Y)).functor

/-- After forgetting to abelian presheaves, module direct image is isomorphic to
right Kan extension along `(toFunctor f).op`. -/
theorem presheafModulePushforward_toPresheaf {X Y : GroupoidsOver S} (f : X ⟶ Y)
    [∀ P : X.totalᵒᵖ ⥤ Type u, (toFunctor f).op.HasPointwiseRightKanExtension P]
    [∀ P : X.totalᵒᵖ ⥤ Ab, HasRightKanExtension (toFunctor f).op P] :
    Nonempty
      (presheafModulePushforward f ⋙
          PresheafOfModules.toPresheaf (structureSheaf Y).obj ≅
        PresheafOfModules.toPresheaf (structureSheaf X).obj ⋙
          (toFunctor f).op.ran) := sorry

end AlgebraicGeometry.GroupoidsOver
