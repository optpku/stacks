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
public import Mathlib.CategoryTheory.Sites.Over
public import ReasLib.AlgebraicGeometry.RingedSite.Basic
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Basic
public import ReasLib.CategoryTheory.Sites.EnoughObjects
public import ReasLib.CategoryTheory.Sites.Cohomology.Objectwise
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Pullback bounded cohomology bases

The site-generic `CategoryTheory.GrothendieckTopology.BoundedCohomologyBasis` controls cohomology
on the selected site itself.  This companion owner records the genuinely different situation in
which a morphism `f : RingedSite.Hom X Y` selects basis objects on `Y` and tests their pullbacks along `f.base`
on `X`.
-/

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe wι w z uX vX uY vY

namespace RingedSite.Hom

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
variable (f : RingedSite.Hom X Y)
variable [@HasSheafify X.carrier X.carrier.str X.siteTopology AddCommGrpCat.{max z vX} inferInstance]
variable [HasExt.{max z vX} ((@Sheaf X.carrier X.carrier.str X.siteTopology AddCommGrpCat.{max z vX} inferInstance))]

/-- A basis on the target site whose selected covering members have bounded higher
cohomology after pullback along `f.base`, for all modules in `A`. -/
@[stacks 0D6V]
structure BoundedCohomologyBasis
    (A : ObjectProperty (ModuleCat.{max z vX} X)) where
  /-- The chosen subset of objects of the target site `Y`. -/
  basis : Set Y.carrier
  /-- Every object of `Y` admits a covering by objects in `basis`. -/
  hasEnoughObjectsWithProperty :
    @GrothendieckTopology.HasEnoughObjectsWithProperty Y.carrier Y.carrier.str Y.siteTopology (· ∈ basis)
  /-- The bound attached to each selected target object. -/
  cohomologyBound {V' : Y.carrier} (hV' : V' ∈ basis) : ℤ
  /-- The selected cofinal covering system of a basis object. -/
  coveringSystem {V' : Y.carrier} (hV' : V' ∈ basis) : Set (FormalCoproduct.{wι} (@Over Y.carrier Y.carrier.str V'))
  /-- Each selected formal coproduct is a covering in the slice topology of `Y`. -/
  coveringSystemIsCover {V' : Y.carrier} (hV' : V' ∈ basis)
      {cover : FormalCoproduct.{wι} (@Over Y.carrier Y.carrier.str V')} (hcover : cover ∈ coveringSystem hV') :
      (@GrothendieckTopology.over Y.carrier Y.carrier.str Y.siteTopology V').CoversTop cover.obj
  /-- The selected coverings are cofinal among all coverings of a basis object. -/
  coveringSystemCofinal {V' : Y.carrier} (hV' : V' ∈ basis) {ι : Type wι} (family : ι → @Over Y.carrier Y.carrier.str V')
      (hfamily : (@GrothendieckTopology.over Y.carrier Y.carrier.str Y.siteTopology V').CoversTop family) :
      ∃ cover : FormalCoproduct.{wι} (@Over Y.carrier Y.carrier.str V'),
        cover ∈ coveringSystem hV' ∧
          Nonempty (cover ⟶ FormalCoproduct.mk ι family)
  /-- Every selected covering member has vanishing pulled-back cohomology above the bound. -/
  higherCohomologyIsZero {V' : Y.carrier} (hV' : V' ∈ basis)
      {cover : FormalCoproduct.{wι} (@Over Y.carrier Y.carrier.str V')} (hcover : cover ∈ coveringSystem hV')
      (i : cover.I) (p : ℕ) (hp : cohomologyBound hV' < p)
      {ℱ : ModuleCat.{max z vX} X} (hℱ : A ℱ) :
      IsZero
        (@Sheaf.cohomologyOverObject X.carrier X.carrier.str X.siteTopology
          ((@SheafOfModules.toSheaf X.carrier X.carrier.str X.siteTopology X.structureSheaf).obj ℱ) inferInstance inferInstance
          (@Functor.obj Y.carrier Y.carrier.str X.carrier X.carrier.str (f.base) (@Over.left Y.carrier Y.carrier.str _ (cover.obj i))) p)

/-- Short namespace-friendly spelling for a pullback bounded cohomology basis. -/
abbrev PullbackBasis (A : ObjectProperty (ModuleCat.{max z vX} X)) :=
  BoundedCohomologyBasis f A

namespace BoundedCohomologyBasis

variable {A : ObjectProperty (ModuleCat.{max z vX} X)}

/-- Construct a pullback bounded cohomology basis from a covering target-site subset,
integer bounds, and cofinal covering systems with the prescribed pulled-back vanishing. -/
def of (basis : Set Y.carrier)
    (hasEnoughObjectsWithProperty :
      @GrothendieckTopology.HasEnoughObjectsWithProperty Y.carrier Y.carrier.str
        Y.siteTopology (· ∈ basis))
    (cohomologyBound : ∀ {V' : Y.carrier}, V' ∈ basis → ℤ)
    (coveringSystem : ∀ {V' : Y.carrier}, V' ∈ basis →
      Set (FormalCoproduct.{wι} (@Over Y.carrier Y.carrier.str V')))
    (coveringSystemIsCover : ∀ {V' : Y.carrier} (hV' : V' ∈ basis)
      {cover : FormalCoproduct.{wι} (@Over Y.carrier Y.carrier.str V')},
      cover ∈ coveringSystem hV' →
        (@GrothendieckTopology.over Y.carrier Y.carrier.str Y.siteTopology V').CoversTop cover.obj)
    (coveringSystemCofinal : ∀ {V' : Y.carrier} (hV' : V' ∈ basis)
      {ι : Type wι} (family : ι → @Over Y.carrier Y.carrier.str V'),
      (@GrothendieckTopology.over Y.carrier Y.carrier.str Y.siteTopology V').CoversTop family →
        ∃ cover : FormalCoproduct.{wι} (@Over Y.carrier Y.carrier.str V'),
          cover ∈ coveringSystem hV' ∧ Nonempty (cover ⟶ FormalCoproduct.mk ι family))
    (higherCohomologyIsZero : ∀ {V' : Y.carrier} (hV' : V' ∈ basis)
      {cover : FormalCoproduct.{wι} (@Over Y.carrier Y.carrier.str V')},
      cover ∈ coveringSystem hV' → ∀ (i : cover.I) (p : ℕ), cohomologyBound hV' < p →
        ∀ {ℱ : ModuleCat.{max z vX} X}, A ℱ →
          IsZero
            (@Sheaf.cohomologyOverObject X.carrier X.carrier.str X.siteTopology
              ((@SheafOfModules.toSheaf X.carrier X.carrier.str X.siteTopology
                X.structureSheaf).obj ℱ) inferInstance inferInstance
              (@Functor.obj Y.carrier Y.carrier.str X.carrier X.carrier.str f.base
                (@Over.left Y.carrier Y.carrier.str _ (cover.obj i))) p)) :
    BoundedCohomologyBasis f A where
  basis := basis
  hasEnoughObjectsWithProperty := hasEnoughObjectsWithProperty
  cohomologyBound := cohomologyBound
  coveringSystem := coveringSystem
  coveringSystemIsCover := coveringSystemIsCover
  coveringSystemCofinal := coveringSystemCofinal
  higherCohomologyIsZero := higherCohomologyIsZero

/-- Test whether a target-site object belongs to the stored bounded cohomology basis. -/
def contains {f : RingedSite.Hom X Y} (basis : BoundedCohomologyBasis f A) (V : Y.carrier) : Prop :=
  V ∈ basis.basis

/-- Membership in a pullback bounded basis agrees with membership in its stored target-site set. -/
@[simp, stacks 0D6V "pullback bounded-cohomology basis membership"]
theorem mem_basis_iff (basis : BoundedCohomologyBasis f A) {V' : Y.carrier} :
    basis.contains V' ↔ V' ∈ basis.basis := sorry

/-- The underlying target-site basis covers every target object. -/
@[stacks 0D6V "pullback bounded-cohomology basis covers the target"]
theorem hasEnoughObjects (basis : BoundedCohomologyBasis f A) :
    @GrothendieckTopology.HasEnoughObjectsWithProperty Y.carrier Y.carrier.str Y.siteTopology basis.contains := sorry

/-- A selected covering-system member is a covering in the target slice topology. -/
@[stacks 0D6V "selected pullback bounded-cohomology covering"]
theorem coveringSystem_isCover (basis : BoundedCohomologyBasis f A)
    {V' : Y.carrier} (hV' : basis.contains V') {cover : FormalCoproduct.{wι} (@Over Y.carrier Y.carrier.str V')}
    (hcover : cover ∈ basis.coveringSystem hV') :
    (@GrothendieckTopology.over Y.carrier Y.carrier.str Y.siteTopology V').CoversTop cover.obj := sorry

/-- A selected covering system refines every covering of a basis object. -/
@[stacks 0D6V "cofinal pullback bounded-cohomology covering system"]
theorem exists_coveringSystem_refinement (basis : BoundedCohomologyBasis f A)
    {V' : Y.carrier} (hV' : basis.contains V') {ι : Type wι} (family : ι → @Over Y.carrier Y.carrier.str V')
    (hfamily : (@GrothendieckTopology.over Y.carrier Y.carrier.str Y.siteTopology V').CoversTop family) :
    ∃ cover : FormalCoproduct.{wι} (@Over Y.carrier Y.carrier.str V'),
      cover ∈ basis.coveringSystem hV' ∧
        Nonempty (cover ⟶ FormalCoproduct.mk ι family) := sorry

/-- Every selected covering member has vanishing pulled-back cohomology above the prescribed bound. -/
@[stacks 0D6V "pullback bounded-cohomology basis vanishing"]
theorem higherCohomology_isZero (basis : BoundedCohomologyBasis f A)
    {V' : Y.carrier} (hV' : basis.contains V') {cover : FormalCoproduct.{wι} (@Over Y.carrier Y.carrier.str V')}
    (hcover : cover ∈ basis.coveringSystem hV') (i : cover.I) (p : ℕ)
    (hp : basis.cohomologyBound hV' < p)
    {ℱ : ModuleCat.{max z vX} X} (hℱ : A ℱ) :
    IsZero
      (@Sheaf.cohomologyOverObject X.carrier X.carrier.str X.siteTopology
        ((@SheafOfModules.toSheaf X.carrier X.carrier.str X.siteTopology X.structureSheaf).obj ℱ) inferInstance inferInstance
        (@Functor.obj Y.carrier Y.carrier.str X.carrier X.carrier.str (f.base) (@Over.left Y.carrier Y.carrier.str _ (cover.obj i))) p) := sorry

end BoundedCohomologyBasis

end RingedSite.Hom

end
