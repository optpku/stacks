/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Limits.FormalCoproducts.Basic
public import Mathlib.CategoryTheory.ObjectProperty.Basic
public import Mathlib.CategoryTheory.Sites.CoversTop.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.AlgebraicGeometry.RingedSite.Localization.Relocalization
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Basic
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Localization
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module
public import ReasLib.CategoryTheory.ObjectProperty.WeakSerre
public import ReasLib.CategoryTheory.Sites.Cohomology.Objectwise
public import ReasLib.CategoryTheory.Sites.EnoughObjects
public import stacks_project.Chap85.Remark_85_15_6_Ringed_variant_Ringed

/-!
# Fiberwise weak Serre subcategories with bounded cohomology

A family `A_U ⊂ Mod(O_U)` of weak Serre subcategories on the localizations of a ringed site,
stable under restriction and local for chosen coverings, together with the stronger fiberwise
bounded-cohomology data of condition (3).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open RingedSite
open RingedSite.Hom
open RingedSite.Localization
open RingedSite.ToposHom

noncomputable section

universe wι u v w

namespace RingedSite

variable {X : RingedSite.{u, v, w}}
variable [UnivLE.{max u v, w}]
variable [X.siteTopology.HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [∀ U : X, (X.siteTopology.over U).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [∀ {U V : X} (f : V ⟶ U),
    (SheafOfModules.restrictScalars.{w} (relocalization X f).structureMap).IsRightAdjoint]

/-- Condition (3) covering data: a basis of objects of `C` with cofinal covering systems and a
bound `d_V`. Fiberwise vanishing on `A_V` is a field of `FiberwiseSerre`, not of this covering
package. -/
structure FiberwiseSerre.BoundedCohomology
    (X : RingedSite.{u, v, w}) where
  /-- The chosen subset `B` of objects of the site. -/
  basis : Set X
  /-- Every object of the site admits a covering by objects in the chosen subset `B`. -/
  hasEnoughObjectsWithProperty :
    X.siteTopology.HasEnoughObjectsWithProperty (· ∈ basis)
  /-- The integer cohomological bound `d_V` attached to a basis object `V`. -/
  cohomologyBound {V : X} (hV : V ∈ basis) : ℤ
  /-- The chosen cofinal system of coverings of a basis object `V`. -/
  coveringSystem {V : X} (hV : V ∈ basis) : Set (FormalCoproduct.{wι} (Over V))
  /-- Each selected element of the cofinal system is an actual covering of `V`. -/
  coveringSystemIsCover {V : X} (hV : V ∈ basis)
      {cover : FormalCoproduct.{wι} (Over V)} (hcover : cover ∈ coveringSystem hV) :
      (X.siteTopology.over V).CoversTop cover.obj
  /-- The selected coverings are cofinal among all coverings of a basis object `V`. -/
  coveringSystemCofinal {V : X} (hV : V ∈ basis) {ι : Type wι} (family : ι → Over V)
      (hfamily : (X.siteTopology.over V).CoversTop family) :
      ∃ cover : FormalCoproduct.{wι} (Over V),
        cover ∈ coveringSystem hV ∧
          Nonempty (cover ⟶ FormalCoproduct.mk ι family)

/-- Package fiberwise bounded-cohomology data from a basis, bounds, and covering systems. -/
def FiberwiseSerre.BoundedCohomology.of (X : RingedSite.{u, v, w})
    (basis : Set X)
    (hasEnoughObjectsWithProperty :
      X.siteTopology.HasEnoughObjectsWithProperty (· ∈ basis))
    (cohomologyBound : {V : X} → V ∈ basis → ℤ)
    (coveringSystem : {V : X} → V ∈ basis → Set (FormalCoproduct.{wι} (Over V)))
    (coveringSystemIsCover : ∀ {V : X} (hV : V ∈ basis)
      {cover : FormalCoproduct.{wι} (Over V)}, cover ∈ coveringSystem hV →
        (X.siteTopology.over V).CoversTop cover.obj)
    (coveringSystemCofinal : ∀ {V : X} (hV : V ∈ basis) {ι : Type wι} (family : ι → Over V),
      (X.siteTopology.over V).CoversTop family →
        ∃ cover : FormalCoproduct.{wι} (Over V),
          cover ∈ coveringSystem hV ∧
            Nonempty (cover ⟶ FormalCoproduct.mk ι family)) :
    FiberwiseSerre.BoundedCohomology.{wι, u, v, w} X where
  basis := basis
  hasEnoughObjectsWithProperty := hasEnoughObjectsWithProperty
  cohomologyBound := cohomologyBound
  coveringSystem := coveringSystem
  coveringSystemIsCover := coveringSystemIsCover
  coveringSystemCofinal := coveringSystemCofinal

/-- A family `A_U ⊂ Mod(O_U)` of weak Serre subcategories satisfying restriction, locality, and
fiberwise bounded cohomological dimension. -/
structure FiberwiseSerre (X : RingedSite.{u, v, w})
    [UnivLE.{max u v, w}]
    [X.siteTopology.HasSheafCompose (CategoryTheory.forget RingCat.{w})]
    [∀ U : X, (X.siteTopology.over U).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
    [∀ {U V : X} (f : V ⟶ U),
      (SheafOfModules.restrictScalars.{w} (relocalization X f).structureMap).IsRightAdjoint]
    where
  /-- The fiberwise weak Serre subcategory `A_U ⊂ Mod(O_U)`. -/
  property : ∀ U : X, ObjectProperty (ModuleCat.{w} (X.localization U))
  /-- Each `A_U` is a weak Serre subcategory of `Mod(O_U)`. -/
  isWeakSerre : ∀ U : X, IsWeakSerreClass (property U)
  /-- Condition (1): restriction `Mod(O_U) ⥤ Mod(O_V)` sends `A_U` into `A_V`. -/
  restriction : ∀ {U V : X} (f : V ⟶ U),
    property U ≤ (property V).inverseImage (relocalization X f).modulePullback
  /-- Condition (2): membership in `A_U` is local for chosen coverings of `U`. -/
  isLocal : ∀ {U : X} {cover : FormalCoproduct.{wι} (Over U)},
    (X.siteTopology.over U).CoversTop cover.obj →
      ∀ F, property U F ↔
        ∀ i : cover.I,
          property (cover.obj i).left
            ((relocalization X (cover.obj i).hom).modulePullback.obj F)
  /-- Condition (3) covering data: basis, bounds, and cofinal covering systems. -/
  bounded : FiberwiseSerre.BoundedCohomology.{wι, u, v, w} X
  /-- Condition (3) vanishing: for `V ∈ B`, `{V_i → V} ∈ Cov_V`, `p > d_V`, and `F ∈ A_V`,
  the cohomology `H^p(V_i, F)` on `C / V` is zero. -/
  higherCohomologyIsZero {V : X} (hV : V ∈ bounded.basis)
      {cover : FormalCoproduct.{wι} (Over V)} (hcover : cover ∈ bounded.coveringSystem hV)
      (i : cover.I) (p : ℕ) (hp : bounded.cohomologyBound hV < p)
      {F : ModuleCat.{w} (X.localization V)} (hF : property V F)
      [(X.siteTopology.over V).HasSheafCompose AddCommGrpCat.uliftFunctor.{v, w}]
      [HasSheafify (X.siteTopology.over V) AddCommGrpCat.{max w v}]
      [HasExt.{max w v} (Sheaf (X.siteTopology.over V) AddCommGrpCat.{max w v})] :
      IsZero
        (Sheaf.cohomologyOverObject
          ((sheafCompose (X.siteTopology.over V) AddCommGrpCat.uliftFunctor.{v, w}).obj
            ((SheafOfModules.toSheaf (X.structureSheaf.over V)).obj F))
          (cover.obj i) p)

/-- Package a fiberwise Serre family from a restriction-stable local family with bounded
cohomology. -/
def FiberwiseSerre.of
    (property : ∀ U : X, ObjectProperty (ModuleCat.{w} (X.localization U)))
    (isWeakSerre : ∀ U : X, IsWeakSerreClass (property U))
    (restriction : ∀ {U V : X} (f : V ⟶ U),
      property U ≤ (property V).inverseImage (relocalization X f).modulePullback)
    (isLocal : ∀ {U : X} {cover : FormalCoproduct.{wι} (Over U)},
      (X.siteTopology.over U).CoversTop cover.obj →
        ∀ F, property U F ↔
          ∀ i : cover.I,
            property (cover.obj i).left
              ((relocalization X (cover.obj i).hom).modulePullback.obj F))
    (bounded : FiberwiseSerre.BoundedCohomology.{wι, u, v, w} X)
    (higherCohomologyIsZero : ∀ {V : X} (hV : V ∈ bounded.basis)
      {cover : FormalCoproduct.{wι} (Over V)} (hcover : cover ∈ bounded.coveringSystem hV)
      (i : cover.I) (p : ℕ) (hp : bounded.cohomologyBound hV < p)
      {F : ModuleCat.{w} (X.localization V)} (hF : property V F)
      [(X.siteTopology.over V).HasSheafCompose AddCommGrpCat.uliftFunctor.{v, w}]
      [HasSheafify (X.siteTopology.over V) AddCommGrpCat.{max w v}]
      [HasExt.{max w v} (Sheaf (X.siteTopology.over V) AddCommGrpCat.{max w v})],
        IsZero
          (Sheaf.cohomologyOverObject
            ((sheafCompose (X.siteTopology.over V) AddCommGrpCat.uliftFunctor.{v, w}).obj
              ((SheafOfModules.toSheaf (X.structureSheaf.over V)).obj F))
            (cover.obj i) p)) :
    FiberwiseSerre.{wι, u, v, w} X where
  property := property
  isWeakSerre := isWeakSerre
  restriction := restriction
  isLocal := isLocal
  bounded := bounded
  higherCohomologyIsZero := higherCohomologyIsZero

namespace FiberwiseSerre

variable (A : FiberwiseSerre.{wι, u, v, w} X)

/-- Restriction along `f : V ⟶ U` sends `A_U` into `A_V`. -/
theorem restriction_le {U V : X} (f : V ⟶ U) :
    A.property U ≤ (A.property V).inverseImage (relocalization X f).modulePullback :=
  A.restriction f

/-- Membership in `A_U` is equivalent to membership of all restrictions along a covering. -/
theorem mem_isLocal {U : X} {cover : FormalCoproduct.{wι} (Over U)}
    (hcover : (X.siteTopology.over U).CoversTop cover.obj)
    (F : ModuleCat.{w} (X.localization U)) :
    A.property U F ↔
      ∀ i : cover.I,
        A.property (cover.obj i).left
          ((relocalization X (cover.obj i).hom).modulePullback.obj F) :=
  A.isLocal hcover F

/-- Condition (3) vanishing on a selected covering member, for modules in `A_V`. -/
theorem higherCohomology_isZero {V : X} (hV : V ∈ A.bounded.basis)
    {cover : FormalCoproduct.{wι} (Over V)} (hcover : cover ∈ A.bounded.coveringSystem hV)
    (i : cover.I) (p : ℕ) (hp : A.bounded.cohomologyBound hV < p)
    {F : ModuleCat.{w} (X.localization V)} (hF : A.property V F)
    [(X.siteTopology.over V).HasSheafCompose AddCommGrpCat.uliftFunctor.{v, w}]
    [HasSheafify (X.siteTopology.over V) AddCommGrpCat.{max w v}]
    [HasExt.{max w v} (Sheaf (X.siteTopology.over V) AddCommGrpCat.{max w v})] :
    IsZero
      (Sheaf.cohomologyOverObject
        ((sheafCompose (X.siteTopology.over V) AddCommGrpCat.uliftFunctor.{v, w}).obj
          ((SheafOfModules.toSheaf (X.structureSheaf.over V)).obj F))
        (cover.obj i) p) :=
  A.higherCohomologyIsZero hV hcover i p hp hF

/-- The global weak Serre subcategory `A ⊂ Mod(O_C)` of modules whose restriction to every
`C / U` lies in `A_U`. -/
def global : ObjectProperty (ModuleCat.{w} X) :=
  fun F ↦ ∀ U : X, A.property U ((localizedRestriction.{w} X U).obj F)

/-- A module on `C` lies in the global subcategory `A` iff every restriction to `C / U` lies in
`A_U`. -/
theorem mem_global_iff (F : ModuleCat.{w} X) :
    A.global F ↔ ∀ U : X, A.property U ((localizedRestriction.{w} X U).obj F) :=
  sorry

/-- The global subcategory `A ⊂ Mod(O_C)` is a weak Serre subcategory. -/
instance global_isWeakSerreClass : IsWeakSerreClass A.global :=
  sorry

/-- The product subcategory `A_K = ∏ A_{U_i}` of modules on `(C / K, O_K)`. -/
def atSR.{ι} (K : FormalCoproduct.{ι} X.carrier) :
    ObjectProperty (SheafOfModules.{w} (AtSR.ringSheaf K)) :=
  fun F ↦ ∀ i : K.I, A.property (K.obj i) ((AtSR.component K i).obj F)

/-- A module on `(C / K, O_K)` lies in `A_K` iff each component lies in `A_{U_i}`. -/
theorem mem_atSR_iff.{ι} (K : FormalCoproduct.{ι} X.carrier)
    (F : SheafOfModules.{w} (AtSR.ringSheaf K)) :
    A.atSR K F ↔ ∀ i : K.I, A.property (K.obj i) ((AtSR.component K i).obj F) :=
  sorry

/-- The product subcategory `A_K` is a weak Serre subcategory. -/
instance atSR_isWeakSerreClass.{ι} (K : FormalCoproduct.{ι} X.carrier)
    [UnivLE.{max ι u v, w}] :
    IsWeakSerreClass (A.atSR K) :=
  sorry


end FiberwiseSerre

end RingedSite

end
