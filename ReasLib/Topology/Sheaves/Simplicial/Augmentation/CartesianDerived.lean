/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Bounded
public import ReasLib.Topology.Sheaves.Simplicial.Cartesian.Abelian
public import ReasLib.Topology.Sheaves.Simplicial.Augmentation.Derived

/-!
# Cartesian restriction of bounded-below derived inverse and direct image

The exact inverse image `a⁻¹` of a Zariski augmentation lands in
`DerivedCategory.Plus.CohomologyIn` of cartesian abelian sheaves, and `Ra_*`
restricts along the inclusion of that full subcategory.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits CategoryTheory.ObjectProperty
open Opposite TopCat
open scoped Simplicial

noncomputable section

universe u

namespace CategoryTheory.SimplicialObject

variable {Y : SimplicialObject TopCat.{u}} {X : TopCat.{u}} (a : Y ⟶ constSpace X)

variable [HasSheafify (zariskiTopology Y) AddCommGrpCat.{u}]
variable [HasSheafify (zariskiTopology (constSpace X)) AddCommGrpCat.{u}]
variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [∀ n : ℕ, HasSheafify (Opens.grothendieckTopology (Y.obj (op ⦋n⦌))) AddCommGrpCat.{u}]

section Plus

variable [(augmentationPushforward a).toBoundedBelowDerived.HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso
      (Sheaf (zariskiTopology Y) AddCommGrpCat.{u}))]

/-- Bounded-below derived inverse image along a Zariski augmentation has cartesian
cohomology in every degree. -/
theorem plusInverseImageDerived_mem_cohomologyIn
    (K : DerivedCategory.Plus (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})) :
    DerivedCategory.Plus.cohomologyIn (cartesianProperty Y AddCommGrpCat.{u})
      ((plusInverseImageDerived a).obj K) :=
  sorry

/-- Bounded-below derived inverse image `a⁻¹`, corestricted to objects with cartesian
cohomology. -/
def plusInverseImageCartesian :
    DerivedCategory.Plus (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) ⥤
      DerivedCategory.Plus.CohomologyIn (cartesianProperty Y AddCommGrpCat.{u}) :=
  (DerivedCategory.Plus.cohomologyIn (cartesianProperty Y AddCommGrpCat.{u})).lift
    (plusInverseImageDerived a) (plusInverseImageDerived_mem_cohomologyIn a)

/-- The underlying object of `plusInverseImageCartesian` is bounded-below derived
inverse image. -/
theorem plusInverseImageCartesian_obj_obj
    (K : DerivedCategory.Plus (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})) :
    ((plusInverseImageCartesian a).obj K).obj = (plusInverseImageDerived a).obj K :=
  rfl

/-- Composing `plusInverseImageCartesian` with the inclusion of cartesian cohomology
recovers bounded-below derived inverse image. -/
def plusInverseImageCartesianCompιIso :
    plusInverseImageCartesian a ⋙
      (DerivedCategory.Plus.cohomologyIn (cartesianProperty Y AddCommGrpCat.{u})).ι ≅
      plusInverseImageDerived a :=
  (DerivedCategory.Plus.cohomologyIn (cartesianProperty Y AddCommGrpCat.{u})).liftCompιIso
    (plusInverseImageDerived a) (plusInverseImageDerived_mem_cohomologyIn a)

/-- Bounded-below `Ra_*`, restricted from objects with cartesian cohomology. -/
def plusDirectImageCartesian :
    DerivedCategory.Plus.CohomologyIn (cartesianProperty Y AddCommGrpCat.{u}) ⥤
      DerivedCategory.Plus (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
  (DerivedCategory.Plus.cohomologyIn (cartesianProperty Y AddCommGrpCat.{u})).ι ⋙
    plusDirectImageDerived a

/-- On objects, `plusDirectImageCartesian` is bounded-below `Ra_*`. -/
theorem plusDirectImageCartesian_obj
    (G : DerivedCategory.Plus.CohomologyIn (cartesianProperty Y AddCommGrpCat.{u})) :
    (plusDirectImageCartesian a).obj G = (plusDirectImageDerived a).obj G.obj :=
  rfl

end Plus

end CategoryTheory.SimplicialObject

end
