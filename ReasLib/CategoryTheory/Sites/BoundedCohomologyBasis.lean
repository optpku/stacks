module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Limits.FormalCoproducts.Basic
public import Mathlib.CategoryTheory.ObjectProperty.Basic
public import Mathlib.CategoryTheory.Sites.CoversTop.Basic
public import Mathlib.CategoryTheory.Sites.Over
public import ReasLib.CategoryTheory.Sites.EnoughObjects
public import ReasLib.CategoryTheory.Sites.Cohomology.Objectwise
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Bounded cohomology bases

`BoundedCohomologyBasis` is the data owner for a basis of site objects together with chosen
cofinal covering systems and uniform higher-cohomology bounds.  Its coefficient universe is
independent of the site and ring universes, and the owner is independent of any chapter file so
that derived-completeness results can consume the same data directly.
-/

open CategoryTheory
open CategoryTheory.Limits

universe wι w z v u

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable [HasSheafify J AddCommGrpCat.{max z v}]
variable [HasExt.{max z v} (Sheaf J AddCommGrpCat.{max z v})]

/-- Situation 21.25.1: a basis of site objects with chosen cofinal coverings and a bound for the
higher cohomology of every selected covering member and every module in `A`. -/
@[stacks 0D6R]
structure BoundedCohomologyBasis
    (𝒪 : Sheaf.{v, w, u, w + 1} J RingCat.{w})
    (A : ObjectProperty (SheafOfModules.{max z v} 𝒪)) where
  /-- The chosen subset `B` of objects of the site. -/
  basis : Set C
  /-- Every object of the site admits a covering by objects in the chosen subset `B`. -/
  hasEnoughObjectsWithProperty :
    J.HasEnoughObjectsWithProperty (· ∈ basis)
  /-- The integer cohomological bound `d_V` attached to a basis object `V`. -/
  cohomologyBound {V : C} (hV : V ∈ basis) : ℤ
  /-- The chosen cofinal system of coverings of a basis object `V`. -/
  coveringSystem {V : C} (hV : V ∈ basis) : Set (FormalCoproduct.{wι} (Over V))
  /-- Each selected element of the cofinal system is an actual covering of `V`. -/
  coveringSystemIsCover {V : C} (hV : V ∈ basis)
      {cover : FormalCoproduct.{wι} (Over V)} (hcover : cover ∈ coveringSystem hV) :
      (J.over V).CoversTop cover.obj
  /-- The selected coverings are cofinal among all coverings of a basis object `V`. -/
  coveringSystemCofinal {V : C} (hV : V ∈ basis) {ι : Type wι} (family : ι → Over V)
      (hfamily : (J.over V).CoversTop family) :
      ∃ cover : FormalCoproduct.{wι} (Over V),
        cover ∈ coveringSystem hV ∧
          Nonempty (cover ⟶ FormalCoproduct.mk ι family)
  /-- Every member of every selected covering has vanishing cohomology above the chosen bound. -/
  higherCohomologyIsZero {V : C} (hV : V ∈ basis)
      {cover : FormalCoproduct.{wι} (Over V)} (hcover : cover ∈ coveringSystem hV)
      (i : cover.I) (p : ℕ) (hp : cohomologyBound hV < p)
      {ℱ : SheafOfModules.{max z v} 𝒪} (hℱ : A ℱ) :
      IsZero
        (Sheaf.cohomologyOverObject
          ((SheafOfModules.toSheaf 𝒪).obj ℱ) (cover.obj i).left p)

/-- A bounded cohomology basis coerces to its underlying set of site objects. -/
instance (𝒪 : Sheaf.{v, w, u, w + 1} J RingCat.{w})
    (A : ObjectProperty (SheafOfModules.{max z v} 𝒪)) :
    CoeOut (BoundedCohomologyBasis 𝒪 A) (Set C) where
  coe h := h.basis

/-- Membership in a bounded cohomology basis is membership in its underlying subset. -/
instance (𝒪 : Sheaf.{v, w, u, w + 1} J RingCat.{w})
    (A : ObjectProperty (SheafOfModules.{max z v} 𝒪)) :
    Membership C (BoundedCohomologyBasis 𝒪 A) where
  mem basis V := V ∈ basis.basis

namespace BoundedCohomologyBasis

variable {𝒪 : Sheaf.{v, w, u, w + 1} J RingCat.{w}}
variable {A : ObjectProperty (SheafOfModules.{max z v} 𝒪)}

/-- Membership in a bounded cohomology basis agrees with membership in its stored subset. -/
@[simp, stacks 0D6R "bounded-cohomology basis membership"]
theorem mem_basis_iff (basis : BoundedCohomologyBasis 𝒪 A) {V : C} :
    V ∈ basis ↔ V ∈ basis.basis := sorry

/-- The underlying subset of a bounded cohomology basis covers every object of the site. -/
@[stacks 0D6R "bounded-cohomology basis covers the site"]
theorem hasEnoughObjects (basis : BoundedCohomologyBasis 𝒪 A) :
    J.HasEnoughObjectsWithProperty (· ∈ basis) := sorry

/-- A selected covering-system member is a covering in the slice topology. -/
@[stacks 0D6R "selected bounded-cohomology covering"]
theorem coveringSystem_isCover (basis : BoundedCohomologyBasis 𝒪 A)
    {V : C} (hV : V ∈ basis) {cover : FormalCoproduct.{wι} (Over V)}
    (hcover : cover ∈ basis.coveringSystem hV) :
    (J.over V).CoversTop cover.obj := sorry

/-- A selected covering system refines every covering of a basis object. -/
@[stacks 0D6R "cofinal bounded-cohomology covering system"]
theorem exists_coveringSystem_refinement (basis : BoundedCohomologyBasis 𝒪 A)
    {V : C} (hV : V ∈ basis) {ι : Type wι} (family : ι → Over V)
    (hfamily : (J.over V).CoversTop family) :
    ∃ cover : FormalCoproduct.{wι} (Over V),
      cover ∈ basis.coveringSystem hV ∧
        Nonempty (cover ⟶ FormalCoproduct.mk ι family) := sorry

/-- Every member of a selected covering satisfies the prescribed higher-cohomology bound. -/
@[stacks 0D6R "bounded-cohomology basis vanishing"]
theorem higherCohomology_isZero (basis : BoundedCohomologyBasis 𝒪 A)
    {V : C} (hV : V ∈ basis) {cover : FormalCoproduct.{wι} (Over V)}
    (hcover : cover ∈ basis.coveringSystem hV) (i : cover.I) (p : ℕ)
    (hp : basis.cohomologyBound hV < p)
    {ℱ : SheafOfModules.{max z v} 𝒪} (hℱ : A ℱ) :
    IsZero
      (Sheaf.cohomologyOverObject
        ((SheafOfModules.toSheaf 𝒪).obj ℱ) (cover.obj i).left p) := sorry

end BoundedCohomologyBasis

end CategoryTheory.GrothendieckTopology

end
