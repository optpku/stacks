/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Simplicial.EtaleCartesianDerived
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Simplicial.FppfDescent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Simplicial.FppfCohomologicalDescent

/-! # Bounded-below cartesian derived descent for fppf hypercoverings

Total étale inverse image along an fppf hypercovering identifies the bounded-below
derived category on the base with objects having cartesian cohomology on the
simplicial algebraic space. Its quasi-inverse is total étale derived direct image.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry
open scoped Simplicial

noncomputable section

namespace AlgebraicGeometry.AlgebraicSpace.Simplicial.EtaleDerived

variable {S : Scheme.{u}} {X : AlgebraicSpace S}
variable {U : SimplicialObject (AlgebraicSpace S)}
variable (a : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj X)

/-- The derived total étale counit of an fppf hypercovering is invertible on
bounded-below objects with cartesian cohomology. -/
theorem plusAdjunction_counit_app_isIso (ha : IsFppfHypercovering a)
    (G : DerivedCategory.Plus.CohomologyIn (EtaleCartesian.IsCartesianAbelian U)) :
    IsIso ((plusAdjunction a).counit.app G.obj) :=
  sorry

/-- The total étale derived unit of an fppf hypercovering gives the unit isomorphism
for inverse image corestricted to cartesian cohomology. -/
def plusCartesianUnitIso (ha : IsFppfHypercovering a) :
    𝟭 (DerivedCategory.Plus (Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1})) ≅
      plusCartesianFunctor a ⋙ plusCartesianInverse a :=
  NatIso.ofComponents
    (fun K ↦
      @asIso _ _ _ _ ((plusDerivedUnit a).app K)
        (plusDerivedUnit_app_isIso a ha K))
    (fun f ↦ (plusDerivedUnit a).naturality f)

/-- The restricted unit component is the canonical total étale derived unit. -/
theorem plusCartesianUnitIso_hom_app (ha : IsFppfHypercovering a)
    (K : DerivedCategory.Plus (Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1})) :
    (plusCartesianUnitIso a ha).hom.app K = (plusDerivedUnit a).app K :=
  rfl

/-- The total étale derived counit of an fppf hypercovering gives the counit
isomorphism on bounded-below objects with cartesian cohomology. -/
def plusCartesianCounitIso (ha : IsFppfHypercovering a) :
    plusCartesianInverse a ⋙ plusCartesianFunctor a ≅
      𝟭 (DerivedCategory.Plus.CohomologyIn (EtaleCartesian.IsCartesianAbelian U)) :=
  NatIso.ofComponents
    (fun G ↦
      (DerivedCategory.Plus.cohomologyIn (EtaleCartesian.IsCartesianAbelian U)).isoMk
        (@asIso _ _ _ _ ((plusAdjunction a).counit.app G.obj)
          (plusAdjunction_counit_app_isIso a ha G)))
    (fun f ↦ by
      apply CategoryTheory.ObjectProperty.hom_ext
      exact (plusAdjunction a).counit.naturality f.hom)

/-- The underlying restricted counit component is the canonical total étale derived counit. -/
theorem plusCartesianCounitIso_hom_app (ha : IsFppfHypercovering a)
    (G : DerivedCategory.Plus.CohomologyIn (EtaleCartesian.IsCartesianAbelian U)) :
    ((plusCartesianCounitIso a ha).hom.app G).hom =
      (plusAdjunction a).counit.app G.obj :=
  rfl

/-- An fppf hypercovering induces an equivalence between bounded-below derived
abelian étale sheaves on the base and objects with cartesian cohomology on its
total étale site, with inverse image and derived direct image as the two functors. -/
def plusCartesianEquivalence (ha : IsFppfHypercovering a) :
    DerivedCategory.Plus (Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1}) ≌
      DerivedCategory.Plus.CohomologyIn (EtaleCartesian.IsCartesianAbelian U) :=
  CategoryTheory.Equivalence.mk (plusCartesianFunctor a) (plusCartesianInverse a)
    (plusCartesianUnitIso a ha) (plusCartesianCounitIso a ha)

/-- The equivalence functor is total étale derived inverse image corestricted to
cartesian cohomology. -/
theorem plusCartesianEquivalence_functor (ha : IsFppfHypercovering a) :
    (plusCartesianEquivalence a ha).functor = plusCartesianFunctor a :=
  rfl

/-- The inverse equivalence functor is total étale derived direct image restricted
to objects with cartesian cohomology. -/
theorem plusCartesianEquivalence_inverse (ha : IsFppfHypercovering a) :
    (plusCartesianEquivalence a ha).inverse = plusCartesianInverse a :=
  rfl

end AlgebraicGeometry.AlgebraicSpace.Simplicial.EtaleDerived
