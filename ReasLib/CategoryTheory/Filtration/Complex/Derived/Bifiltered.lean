module

public import ReasLib.CategoryTheory.Filtration.Bifiltered.Complex
public import ReasLib.CategoryTheory.Filtration.Complex.Derived.InverseSystem
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Bifiltered realizations in a derived category

A bifiltered realization uses one bifiltered complex and one identification of its common
underlying complex with the target derived object. The two tower identifications and their
compatibility equations are stored symmetrically.
-/

open CategoryTheory.Limits

noncomputable section

universe t w v u

namespace CategoryTheory

namespace BifilteredComplex

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{t} A]

/-- A common realization of two derived inverse systems and their compatible maps to one
derived object. -/
@[stacks 0ESK "bifiltered realization owner"]
structure Realization
    {system system' : ℤᵒᵖ ⥤ DerivedCategory A} (E : DerivedCategory A)
    (π : system ⟶ (Functor.const ℤᵒᵖ).obj E)
    (π' : system' ⟶ (Functor.const ℤᵒᵖ).obj E) where
  /-- The bifiltered cochain complex realizing both systems. -/
  complex : BifilteredComplex A
  /-- The common underlying cochain complex represents the common target. -/
  pointIso : DerivedCategory.Q.obj complex.underlying ≅ E
  /-- The first derived filtration-stage tower is the first prescribed system. -/
  firstTowerIso : complex.first.derivedTower ≅ system
  /-- The second derived filtration-stage tower is the second prescribed system. -/
  secondTowerIso : complex.second.derivedTower ≅ system'
  /-- The first stage and common-point identifications respect the first cocone. -/
  firstFac (i : ℤᵒᵖ) :
    DerivedCategory.Q.map (complex.firstInclusion i.unop) ≫ pointIso.hom =
      firstTowerIso.hom.app i ≫ π.app i
  /-- The second stage and common-point identifications respect the second cocone. -/
  secondFac (i : ℤᵒᵖ) :
    DerivedCategory.Q.map (complex.secondInclusion i.unop) ≫ pointIso.hom =
      secondTowerIso.hom.app i ≫ π'.app i

namespace Realization

/-- Retain the first filtered realization from a bifiltered realization. -/
def first
    {system system' : ℤᵒᵖ ⥤ DerivedCategory A} {E : DerivedCategory A}
    {π : system ⟶ (Functor.const ℤᵒᵖ).obj E}
    {π' : system' ⟶ (Functor.const ℤᵒᵖ).obj E}
    (R : Realization E π π') : FilteredComplex.Realization (Cocone.mk E π) where
  complex := R.complex.first
  towerIso := R.firstTowerIso
  pointIso := R.pointIso
  fac := R.firstFac

/-- Retain the second filtered realization from a bifiltered realization. -/
def second
    {system system' : ℤᵒᵖ ⥤ DerivedCategory A} {E : DerivedCategory A}
    {π : system ⟶ (Functor.const ℤᵒᵖ).obj E}
    {π' : system' ⟶ (Functor.const ℤᵒᵖ).obj E}
    (R : Realization E π π') : FilteredComplex.Realization (Cocone.mk E π') where
  complex := R.complex.second
  towerIso := R.secondTowerIso
  pointIso := R.pointIso
  fac := R.secondFac

/-- Exchange the two systems and filtrations in a bifiltered realization. -/
def swap
    {system system' : ℤᵒᵖ ⥤ DerivedCategory A} {E : DerivedCategory A}
    {π : system ⟶ (Functor.const ℤᵒᵖ).obj E}
    {π' : system' ⟶ (Functor.const ℤᵒᵖ).obj E}
    (R : Realization E π π') : Realization E π' π where
  complex := R.complex.swap
  pointIso := R.pointIso
  firstTowerIso := R.secondTowerIso
  secondTowerIso := R.firstTowerIso
  firstFac := R.secondFac
  secondFac := R.firstFac

/-- Both filtered views of a bifiltered realization use the same point identification. -/
theorem first_pointIso
    {system system' : ℤᵒᵖ ⥤ DerivedCategory A} {E : DerivedCategory A}
    {π : system ⟶ (Functor.const ℤᵒᵖ).obj E}
    {π' : system' ⟶ (Functor.const ℤᵒᵖ).obj E}
    (R : Realization E π π') : R.first.pointIso = R.pointIso := sorry

/-- The second filtered view uses the common point identification. -/
theorem second_pointIso
    {system system' : ℤᵒᵖ ⥤ DerivedCategory A} {E : DerivedCategory A}
    {π : system ⟶ (Functor.const ℤᵒᵖ).obj E}
    {π' : system' ⟶ (Functor.const ℤᵒᵖ).obj E}
    (R : Realization E π π') : R.second.pointIso = R.pointIso := sorry

/-- Exchanging the systems and filtrations twice recovers the original realization. -/
theorem swap_swap
    {system system' : ℤᵒᵖ ⥤ DerivedCategory A} {E : DerivedCategory A}
    {π : system ⟶ (Functor.const ℤᵒᵖ).obj E}
    {π' : system' ⟶ (Functor.const ℤᵒᵖ).obj E}
    (R : Realization E π π') : R.swap.swap = R := sorry

end Realization

end BifilteredComplex

namespace BifilteredComplex.Realization

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{t} A]

/-- Two derived cocones with isomorphic points admit a common bifiltered realization after
transporting the second cocone to the first point. -/
@[stacks 0ESK "point-isomorphic form"]
theorem nonemptyOfPointIso
    [IsGrothendieckAbelian.{w} A]
    {system system' : ℤᵒᵖ ⥤ DerivedCategory A}
    (c : Cocone system) (c' : Cocone system') (e : c'.pt ≅ c.pt) :
    Nonempty
      (BifilteredComplex.Realization c.pt c.ι
        (c'.ι ≫ (Functor.const ℤᵒᵖ).map e.hom)) := sorry

/-- Lemma 19.13.13: two inverse systems mapping compatibly to the same derived object admit a
common bifiltered-complex realization using one shared representative of the target. -/
@[stacks 0ESK "common-point form"]
theorem nonempty [IsGrothendieckAbelian.{w} A]
    {system system' : ℤᵒᵖ ⥤ DerivedCategory A} (E : DerivedCategory A)
    (π : system ⟶ (Functor.const ℤᵒᵖ).obj E)
    (π' : system' ⟶ (Functor.const ℤᵒᵖ).obj E) :
    Nonempty (BifilteredComplex.Realization E π π') := sorry

end BifilteredComplex.Realization

end CategoryTheory
