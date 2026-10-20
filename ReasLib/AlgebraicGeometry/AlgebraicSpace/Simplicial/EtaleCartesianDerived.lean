/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Simplicial.EtaleCartesian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Simplicial.EtaleDerived
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Bounded
public import ReasLib.CategoryTheory.ObjectProperty.WeakSerre

/-! # Cartesian cohomology and total étale derived functors

Cartesian abelian sheaves form a weak Serre subcategory. The bounded-below derived
inverse image of a total étale augmentation has cartesian cohomology, and derived
direct image restricts to the full subcategory of objects with cartesian cohomology.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry
open scoped Simplicial

noncomputable section

namespace AlgebraicGeometry.AlgebraicSpace.Simplicial

variable {S : Scheme.{u}} {X : AlgebraicSpace S}
variable {U : SimplicialObject (AlgebraicSpace S)}

/-- Cartesian abelian sheaves on a simplicial algebraic space form a weak Serre subcategory. -/
instance EtaleCartesian.isWeakSerreClass (U : SimplicialObject (AlgebraicSpace S)) :
    ObjectProperty.IsWeakSerreClass (EtaleCartesian.IsCartesianAbelian U) :=
  sorry

namespace EtaleDerived

variable (a : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj X)

/-- Bounded-below derived inverse image along a total étale augmentation has cartesian
cohomology in every degree. -/
theorem plusInverseImage_mem_cohomologyIn
    (K : DerivedCategory.Plus (Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1})) :
    DerivedCategory.Plus.cohomologyIn (EtaleCartesian.IsCartesianAbelian U)
      ((plusInverseImage a).obj K) :=
  sorry

/-- Bounded-below derived inverse image of total étale augmentation, corestricted to
objects with cartesian cohomology. -/
def plusCartesianFunctor :
    DerivedCategory.Plus (Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory.Plus.CohomologyIn (EtaleCartesian.IsCartesianAbelian U) :=
  (DerivedCategory.Plus.cohomologyIn (EtaleCartesian.IsCartesianAbelian U)).lift
    (plusInverseImage a) (plusInverseImage_mem_cohomologyIn a)

/-- The underlying object of corestricted inverse image is total étale derived inverse image. -/
theorem plusCartesianFunctor_obj
    (K : DerivedCategory.Plus (Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1})) :
    ((plusCartesianFunctor a).obj K).obj = (plusInverseImage a).obj K :=
  rfl

/-- Bounded-below derived direct image of total étale augmentation, restricted to
objects with cartesian cohomology. -/
def plusCartesianInverse :
    DerivedCategory.Plus.CohomologyIn (EtaleCartesian.IsCartesianAbelian U) ⥤
      DerivedCategory.Plus (Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1}) :=
  (DerivedCategory.Plus.cohomologyIn (EtaleCartesian.IsCartesianAbelian U)).ι ⋙
    plusDirectImage a

/-- Restricted derived direct image applies total étale derived direct image to the
underlying bounded-below object. -/
theorem plusCartesianInverse_obj
    (G : DerivedCategory.Plus.CohomologyIn (EtaleCartesian.IsCartesianAbelian U)) :
    (plusCartesianInverse a).obj G = (plusDirectImage a).obj G.obj :=
  rfl

end EtaleDerived

end AlgebraicGeometry.AlgebraicSpace.Simplicial
