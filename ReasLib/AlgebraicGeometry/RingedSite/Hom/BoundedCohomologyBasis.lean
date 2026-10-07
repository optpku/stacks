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
which a morphism `f : X ⟶ Y` selects basis objects on `Y` and tests their pullbacks along `f.base`
on `X`.
-/

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe wι w z uX vX uY vY

namespace RingedSite.Hom

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
variable (f : RingedSite.Hom X Y)
variable [HasSheafify X.siteTopology AddCommGrpCat.{max z vX}]
variable [HasExt.{max z vX} (Sheaf X.siteTopology AddCommGrpCat.{max z vX})]

/-- Situation 21.25.5: a basis on `Y` whose selected covering members have bounded higher
cohomology after pullback along `f.base`, for all modules in `A`. -/
@[stacks 0D6V]
structure BoundedCohomologyBasis
    (A : ObjectProperty (ModuleCat.{max z vX} X)) where
  /-- The chosen subset of objects of the target site `Y`. -/
  basis : Set Y
  /-- Every object of `Y` admits a covering by objects in `basis`. -/
  hasEnoughObjectsWithProperty :
    Y.siteTopology.HasEnoughObjectsWithProperty (· ∈ basis)
  /-- The bound attached to each selected target object. -/
  cohomologyBound {V' : Y} (hV' : V' ∈ basis) : ℤ
  /-- The selected cofinal covering system of a basis object. -/
  coveringSystem {V' : Y} (hV' : V' ∈ basis) : Set (FormalCoproduct.{wι} (Over V'))
  /-- Each selected formal coproduct is a covering in the slice topology of `Y`. -/
  coveringSystemIsCover {V' : Y} (hV' : V' ∈ basis)
      {cover : FormalCoproduct.{wι} (Over V')} (hcover : cover ∈ coveringSystem hV') :
      (Y.siteTopology.over V').CoversTop cover.obj
  /-- The selected coverings are cofinal among all coverings of a basis object. -/
  coveringSystemCofinal {V' : Y} (hV' : V' ∈ basis) {ι : Type wι} (family : ι → Over V')
      (hfamily : (Y.siteTopology.over V').CoversTop family) :
      ∃ cover : FormalCoproduct.{wι} (Over V'),
        cover ∈ coveringSystem hV' ∧
          Nonempty (cover ⟶ FormalCoproduct.mk ι family)
  /-- Every selected covering member has vanishing pulled-back cohomology above the bound. -/
  higherCohomologyIsZero {V' : Y} (hV' : V' ∈ basis)
      {cover : FormalCoproduct.{wι} (Over V')} (hcover : cover ∈ coveringSystem hV')
      (i : cover.I) (p : ℕ) (hp : cohomologyBound hV' < p)
      {ℱ : ModuleCat.{max z vX} X} (hℱ : A ℱ) :
      IsZero
        (Sheaf.cohomologyOverObject
          ((SheafOfModules.toSheaf X.structureSheaf).obj ℱ)
          (f.base.obj (cover.obj i).left) p)

/-- A pullback bounded basis coerces to its underlying target-site subset. -/
instance (A : ObjectProperty (ModuleCat.{max z vX} X)) :
    CoeOut (BoundedCohomologyBasis f A) (Set Y) where
  coe h := h.basis

/-- Membership in a pullback bounded basis is membership in its target-site subset. -/
instance (A : ObjectProperty (ModuleCat.{max z vX} X)) :
    Membership Y (BoundedCohomologyBasis f A) where
  mem basis V := V ∈ basis.basis

/-- Short namespace-friendly spelling for a pullback bounded cohomology basis. -/
abbrev PullbackBasis (A : ObjectProperty (ModuleCat.{max z vX} X)) :=
  BoundedCohomologyBasis f A

namespace BoundedCohomologyBasis

variable {A : ObjectProperty (ModuleCat.{max z vX} X)}

/-- Membership in a pullback bounded basis agrees with membership in its stored target-site set. -/
@[simp, stacks 0D6V "pullback bounded-cohomology basis membership"]
theorem mem_basis_iff (basis : BoundedCohomologyBasis f A) {V' : Y} :
    V' ∈ basis ↔ V' ∈ basis.basis := sorry

/-- The underlying target-site basis covers every target object. -/
@[stacks 0D6V "pullback bounded-cohomology basis covers the target"]
theorem hasEnoughObjects (basis : BoundedCohomologyBasis f A) :
    Y.siteTopology.HasEnoughObjectsWithProperty (· ∈ basis) := sorry

/-- A selected covering-system member is a covering in the target slice topology. -/
@[stacks 0D6V "selected pullback bounded-cohomology covering"]
theorem coveringSystem_isCover (basis : BoundedCohomologyBasis f A)
    {V' : Y} (hV' : V' ∈ basis) {cover : FormalCoproduct.{wι} (Over V')}
    (hcover : cover ∈ basis.coveringSystem hV') :
    (Y.siteTopology.over V').CoversTop cover.obj := sorry

/-- A selected covering system refines every covering of a basis object. -/
@[stacks 0D6V "cofinal pullback bounded-cohomology covering system"]
theorem exists_coveringSystem_refinement (basis : BoundedCohomologyBasis f A)
    {V' : Y} (hV' : V' ∈ basis) {ι : Type wι} (family : ι → Over V')
    (hfamily : (Y.siteTopology.over V').CoversTop family) :
    ∃ cover : FormalCoproduct.{wι} (Over V'),
      cover ∈ basis.coveringSystem hV' ∧
        Nonempty (cover ⟶ FormalCoproduct.mk ι family) := sorry

/-- Every selected covering member has vanishing pulled-back cohomology above the prescribed bound. -/
@[stacks 0D6V "pullback bounded-cohomology basis vanishing"]
theorem higherCohomology_isZero (basis : BoundedCohomologyBasis f A)
    {V' : Y} (hV' : V' ∈ basis) {cover : FormalCoproduct.{wι} (Over V')}
    (hcover : cover ∈ basis.coveringSystem hV') (i : cover.I) (p : ℕ)
    (hp : basis.cohomologyBound hV' < p)
    {ℱ : ModuleCat.{max z vX} X} (hℱ : A ℱ) :
    IsZero
      (Sheaf.cohomologyOverObject
        ((SheafOfModules.toSheaf X.structureSheaf).obj ℱ)
        (f.base.obj (cover.obj i).left) p) := sorry

end BoundedCohomologyBasis

end RingedSite.Hom

end
