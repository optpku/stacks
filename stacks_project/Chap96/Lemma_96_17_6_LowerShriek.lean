/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Sites.Pullback
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings.Equivalence
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Restriction
public import ReasLib.AlgebraicGeometry.RingedSite.Module.LowerShriek
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom
public import stacks_project.Chap96.Lemma_96_6_2_RingedTopos

/-!
# Module inverse image and lower shriek on associated τ-sites

A 1-morphism of categories fibred in groupoids over `(Sch/S)_fppf` induces, on
each associated `τ`-site, the module inverse image `f^*` landing in
`Mod(X_τ, O_X)` and its left adjoint `f_!`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Functor FiberedCategoryOver.Groupoids
open RingedSite.Cocontinuous
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}
variable {X Y : GroupoidsOver S} (f : X ⟶ Y) (τ : StandardTopology)

/-- The cartesian total functor of a 1-morphism commutes strictly with the
projections. -/
abbrev toCartesianBasedFunctor_comm :
    (toCartesianBasedFunctor f).toFunctor ⋙ Y.p = X.p :=
  (toCartesianBasedFunctor f).toBasedFunctor.w

/-- The identification `f⁻¹ O_Y ≅ O_X` of associated `τ`-structure sheaves along
the cartesian total functor of a 1-morphism. -/
def associatedStructureSheafInverseImageIso_cartesian :
    ((toCartesianBasedFunctor f).toFunctor.sheafPushforwardContinuous RingCat.{u}
        (X.associatedTopology τ) (Y.associatedTopology τ)).obj
      (associatedStructureSheaf Y τ) ≅ associatedStructureSheaf X τ :=
  (sheafPushforwardContinuousComp' (eqToIso (toCartesianBasedFunctor_comm f))
      RingCat.{u} (X.associatedTopology τ) (Y.associatedTopology τ)
      (τ.overTopology S)).app
    (StandardTopology.Big.structureSheaf τ S)

/-- The module inverse image `f^* : Mod(Y_τ, O_Y) ⥤ Mod(X_τ, O_X)` along a
1-morphism of categories fibred in groupoids, obtained by restricting scalars
along `f⁻¹ O_Y ≅ O_X`. -/
abbrev associatedModuleInverseImage :
    SheafOfModules.{u + 1} (associatedStructureSheaf Y τ) ⥤
      SheafOfModules.{u + 1} (associatedStructureSheaf X τ) :=
  moduleInverseImage (toCartesianBasedFunctor f).toFunctor (associatedStructureSheaf Y τ) ⋙
    SheafOfModules.restrictScalars
      (associatedStructureSheafInverseImageIso_cartesian f τ).inv

/-- The module lower shriek `f_! : Mod(X_τ, O_X) ⥤ Mod(Y_τ, O_Y)`, the chosen
left adjoint of `associatedModuleInverseImage`. -/
abbrev associatedModuleLowerShriek :
    SheafOfModules.{u + 1} (associatedStructureSheaf X τ) ⥤
      SheafOfModules.{u + 1} (associatedStructureSheaf Y τ) :=
  (associatedModuleInverseImage f τ).leftAdjoint

/-- The adjunction `f_! ⊣ f^*` of associated `τ`-module sheaves. -/
def associatedModuleLowerShriek_adjunction :
    associatedModuleLowerShriek f τ ⊣ associatedModuleInverseImage f τ :=
  Adjunction.ofIsRightAdjoint (associatedModuleInverseImage f τ)

/-- The Hom equivalence induced by the associated `τ`-module lower-shriek
adjunction. -/
def associatedModuleLowerShriek_homEquiv
    (F : SheafOfModules.{u + 1} (associatedStructureSheaf X τ))
    (G : SheafOfModules.{u + 1} (associatedStructureSheaf Y τ)) :
    ((associatedModuleLowerShriek f τ).obj F ⟶ G) ≃
      (F ⟶ (associatedModuleInverseImage f τ).obj G) :=
  (associatedModuleLowerShriek_adjunction f τ).homEquiv F G

section Comparison

variable [∀ P : X.totalᵒᵖ ⥤ AddCommGrpCat.{u + 1},
    (toCartesianBasedFunctor f).toFunctor.op.HasLeftKanExtension P]
variable [HasWeakSheafify (Y.associatedTopology τ) AddCommGrpCat.{u + 1}]

/-- Forgetting module structure identifies `associatedModuleInverseImage` with
abelian inverse image. -/
def associatedModuleInverseImage_underlyingIso :
    associatedModuleInverseImage f τ ⋙
        SheafOfModules.toSheaf (associatedStructureSheaf X τ) ≅
      SheafOfModules.toSheaf (associatedStructureSheaf Y τ) ⋙
        (toCartesianBasedFunctor f).toFunctor.sheafPushforwardContinuous
          AddCommGrpCat.{u + 1} (X.associatedTopology τ) (Y.associatedTopology τ) :=
  isoWhiskerLeft
      (moduleInverseImage (toCartesianBasedFunctor f).toFunctor
        (associatedStructureSheaf Y τ))
      (SheafOfModules.restrictScalarsCompToSheaf
        (associatedStructureSheafInverseImageIso_cartesian f τ).inv) ≪≫
    moduleInverseImage.underlyingIso (toCartesianBasedFunctor f).toFunctor
      (associatedStructureSheaf Y τ)

/-- The canonical comparison from abelian `f_!` after forgetting to forgetting
after module `f_!`. -/
def associatedModuleLowerShriek_underlyingComparison :
    SheafOfModules.toSheaf (associatedStructureSheaf X τ) ⋙
        (toCartesianBasedFunctor f).toFunctor.sheafPullback AddCommGrpCat.{u + 1}
          (X.associatedTopology τ) (Y.associatedTopology τ) ⟶
      associatedModuleLowerShriek f τ ⋙
        SheafOfModules.toSheaf (associatedStructureSheaf Y τ) :=
  ((mateEquiv (associatedModuleLowerShriek_adjunction f τ)
        ((toCartesianBasedFunctor f).toFunctor.sheafAdjunctionContinuous
          AddCommGrpCat.{u + 1} (X.associatedTopology τ)
          (Y.associatedTopology τ))).symm
      (associatedModuleInverseImage_underlyingIso f τ).hom).natTrans

end Comparison

end AlgebraicGeometry.GroupoidsOver
