module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.CategoryTheory.IsomorphismClasses
public import ReasLib.Algebra.Category.Grp.Presheaf.Derived
public import ReasLib.Algebra.Homology.DerivedCategory.AddCommGrpCat
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.ChangeOfRings
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Underlying
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Colimit.Point
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact
public import ReasLib.CategoryTheory.Sites.Chaotic
public import stacks_project.Chap92.«92_4_0_1_Morphism»
import Mathlib.Tactic.CrossRefAttribute

/-!
# Change of rings after derived lower shriek on the polynomial site

Lemma 92.5.6 identifies `Lπ!(F)` with `Lπ!(Li^* F)` and with
`Lπ!(F ⊗_O^L underline{B})` in `D(Ab)`, for any `O`-module `F` on `C_{B/A}`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CommAlgCat.Over.Polynomial
open RingedSite.Hom
open SheafOfModules
open SheafOfModules.RingedSite
open scoped CategoryTheory

noncomputable section

universe u

namespace CommAlgCat.Over.Polynomial
namespace Site

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
variable [HasColimitsOfShape (site A B)ᵒᵖ AddCommGrpCat.{u + 1}]
variable [Functor.HasLeftDerivedFunctor
    (categoryOverPointColimitToDerived (site A B) AddCommGrpCat.{u + 1})
    (HomotopyCategory.quasiIso ((site A B)ᵒᵖ ⥤ AddCommGrpCat.{u + 1})
      (ComplexShape.up ℤ))]

/-- The standard derived-category model on `O`-modules over `C_{B/A}`. -/
instance moduleCat_hasDerivedCategory_ringedSite :
    HasDerivedCategory.{u + 2} (RingedSite.ModuleCat.{u + 1} (ringedSite A B)) :=
  moduleCat_hasDerivedCategory.{u + 1, u + 1, u, u + 1} (ringedSite A B)

/-- The standard derived-category model on `underline{B}`-modules over `C_{B/A}`. -/
instance moduleCat_hasDerivedCategory_constantRingedSite :
    HasDerivedCategory.{u + 2} (RingedSite.ModuleCat.{u + 1} (constantRingedSite A B)) :=
  moduleCat_hasDerivedCategory.{u + 1, u + 1, u, u + 1} (constantRingedSite A B)

/-- Chaotic sheaf-to-presheaf finite colimits on `(Sh(C), O)`. -/
instance preservesFiniteColimits_sheafToPresheaf_ringedSite :
    PreservesFiniteColimits
      (sheafToPresheaf (ringedSite A B).siteTopology AddCommGrpCat.{u + 1}) :=
  sheafToPresheaf_bot_preservesFiniteColimits

/-- Chaotic sheaf-to-presheaf finite colimits on `(Sh(C), underline{B})`. -/
instance preservesFiniteColimits_sheafToPresheaf_constantRingedSite :
    PreservesFiniteColimits
      (sheafToPresheaf (constantRingedSite A B).siteTopology AddCommGrpCat.{u + 1}) :=
  sheafToPresheaf_bot_preservesFiniteColimits

/-- Additive derived lower shriek `Lπ!` of `O`-modules on `C_{B/A}`, landing in `D(Ab)`. -/
noncomputable abbrev lowerShriek :
    ModuleDerived.{u + 1} (ringedSite A B) ⥤ DerivedCategory AddCommGrpCat.{u + 1} :=
  (underlyingAbelianPresheafExactFunctor.{u + 1} (ringedSite A B)).mapDerivedCategory ⋙
    categoryOverPointDerivedColimit (site A B) AddCommGrpCat.{u + 1}

/-- Additive derived lower shriek `Lπ!` of `underline{B}`-modules on `C_{B/A}`. -/
noncomputable abbrev lowerShriekConstant :
    ModuleDerived.{u + 1} (constantRingedSite A B) ⥤
      DerivedCategory AddCommGrpCat.{u + 1} :=
  (underlyingAbelianPresheafExactFunctor.{u + 1} (constantRingedSite A B)).mapDerivedCategory ⋙
    categoryOverPointDerivedColimit (site A B) AddCommGrpCat.{u + 1}

/-- Derived extension of scalars along `i♯ : O ⟶ underline{B}`, i.e. both `Li^*` and
`(-) ⊗_O^L underline{B}` on `D(O)`. -/
noncomputable abbrev changeOfRings :
    ModuleDerived.{u + 1} (ringedSite A B) ⥤
      ModuleDerived.{u + 1} (constantRingedSite A B) :=
  SameSite.pullbackDerived.{u + 1, u, u + 1, u + 1}
    (structureSheafMapLift A B)

/-- Degree-zero embedding of an `O`-module into `D(O)`. -/
noncomputable abbrev single (F : RingedSite.ModuleCat.{u + 1} (ringedSite A B)) :
    ModuleDerived.{u + 1} (ringedSite A B) :=
  (DerivedCategory.singleFunctor (RingedSite.ModuleCat.{u + 1} (ringedSite A B))
      (0 : ℤ)).obj F

/-- The comparison `Lπ!(O) ⟶ Lπ!(underline{B})` in `D(Ab)` induced by `i♯`. -/
noncomputable abbrev unitComparison :=
  (lowerShriek A B).map
    ((DerivedCategory.singleFunctor (RingedSite.ModuleCat.{u + 1} (ringedSite A B))
        (0 : ℤ)).map
      (unitToPushforwardObjUnit
        (ringedSiteStructureMap.{u + 1, u, u + 1}
          (structureSheafMapLift A B))))

/-- The comparison `Lπ!(O) ⟶ Lπ!(underline{B})` in `D(Ab)` induced by `i♯` is an
isomorphism. -/
instance structureSheafMap_unitComparison_isIso : IsIso (unitComparison A B) :=
  sorry

/-- The unit comparison is `Lπ!` applied to the extension-of-scalars unit on `O`. -/
theorem unitComparison_eq :
    unitComparison A B =
      (lowerShriek A B).map
        ((DerivedCategory.singleFunctor (RingedSite.ModuleCat.{u + 1} (ringedSite A B))
            (0 : ℤ)).map
          (unitToPushforwardObjUnit
            (ringedSiteStructureMap.{u + 1, u, u + 1}
              (structureSheafMapLift A B)))) :=
  sorry

/-- Lemma 92.5.6. Let `A → B` be a ring map. Let `π`, `O`, `underline{B}` be as in
92.4.0.1. For any `O`-module `F` we have
`Lπ!(F) = Lπ!(Li^* F) = Lπ!(F ⊗_O^L underline{B})` in `D(Ab)`.
Both source comparisons are derived extension of scalars along `i♯`. -/
@[stacks 08QJ]
theorem lowerShriek_changeOfRings_obj
    (F : RingedSite.ModuleCat.{u + 1} (ringedSite A B)) :
    IsIsomorphic ((lowerShriek A B).obj (single A B F))
      ((lowerShriekConstant A B).obj ((changeOfRings A B).obj (single A B F))) :=
  sorry

/-- Derived-object form of the same comparison: for `K` in `D(O)`, `Lπ!(K)` is
isomorphic in `D(Ab)` to `Lπ!` of the derived extension of scalars of `K` along
`i♯`. -/
theorem lowerShriek_changeOfRings (K : ModuleDerived.{u + 1} (ringedSite A B)) :
    IsIsomorphic ((lowerShriek A B).obj K)
      ((lowerShriekConstant A B).obj ((changeOfRings A B).obj K)) :=
  sorry

end Site
end CommAlgCat.Over.Polynomial
