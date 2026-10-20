/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Simplicial.EtaleCartesianDerived
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Simplicial.ProperCohomologicalDescent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Simplicial.ProperDescent

/-! # Bounded-below cartesian derived descent for proper hypercoverings

Total étale inverse image along a proper hypercovering identifies the bounded-below
derived category on the base with objects having cartesian cohomology on the
simplicial algebraic space. Its quasi-inverse is total étale derived direct image.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry
open scoped Simplicial

noncomputable section

namespace AlgebraicGeometry.AlgebraicSpace.Simplicial

variable {S : Scheme.{u}} {X : AlgebraicSpace S}
variable {U : SimplicialObject (AlgebraicSpace S)}
variable (a : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj X)

/-- The derived total étale counit of a proper hypercovering is invertible on
bounded-below objects with cartesian cohomology. -/
theorem properPlusDerivedCounit_app_isIso (ha : IsProperHypercovering a)
    (K : DerivedCategory.Plus.CohomologyIn (EtaleCartesian.IsCartesianAbelian U)) :
    IsIso ((EtaleDerived.plusAdjunction a).counit.app K.obj) := sorry

/-- The derived total étale unit of a proper hypercovering gives the unit isomorphism
for inverse image corestricted to cartesian cohomology. -/
def properPlusCartesianUnitIso (ha : IsProperHypercovering a) :
    𝟭 (DerivedCategory.Plus (Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1})) ≅
      EtaleDerived.plusCartesianFunctor a ⋙ EtaleDerived.plusCartesianInverse a :=
  @asIso _ _ _ _ (EtaleDerived.plusDerivedUnit a) (properPlusDerivedUnit_isIso a ha)

/-- The restricted unit component is the canonical total étale derived unit. -/
theorem properPlusCartesianUnitIso_hom_app (ha : IsProperHypercovering a)
    (K : DerivedCategory.Plus (Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1})) :
    (properPlusCartesianUnitIso a ha).hom.app K =
      (EtaleDerived.plusDerivedUnit a).app K := sorry

/-- The lifted derived counit components of a proper hypercovering are natural on
bounded-below objects with cartesian cohomology. -/
private theorem properPlusCartesianCounitIso_naturality (ha : IsProperHypercovering a)
    {K L : DerivedCategory.Plus.CohomologyIn (EtaleCartesian.IsCartesianAbelian U)}
    (f : K ⟶ L) :
    (EtaleDerived.plusCartesianInverse a ⋙ EtaleDerived.plusCartesianFunctor a).map f ≫
        ((DerivedCategory.Plus.cohomologyIn (EtaleCartesian.IsCartesianAbelian U)).isoMk
          (@asIso _ _ _ _ ((EtaleDerived.plusAdjunction a).counit.app L.obj)
            (properPlusDerivedCounit_app_isIso a ha L))).hom =
      ((DerivedCategory.Plus.cohomologyIn (EtaleCartesian.IsCartesianAbelian U)).isoMk
        (@asIso _ _ _ _ ((EtaleDerived.plusAdjunction a).counit.app K.obj)
          (properPlusDerivedCounit_app_isIso a ha K))).hom ≫
        (𝟭 (DerivedCategory.Plus.CohomologyIn (EtaleCartesian.IsCartesianAbelian U))).map f :=
  sorry

/-- The derived total étale counit of a proper hypercovering gives the counit
isomorphism on bounded-below objects with cartesian cohomology. -/
@[no_expose]
def properPlusCartesianCounitIso (ha : IsProperHypercovering a) :
    EtaleDerived.plusCartesianInverse a ⋙ EtaleDerived.plusCartesianFunctor a ≅
      𝟭 (DerivedCategory.Plus.CohomologyIn (EtaleCartesian.IsCartesianAbelian U)) :=
  NatIso.ofComponents
    (fun K ↦
      (DerivedCategory.Plus.cohomologyIn (EtaleCartesian.IsCartesianAbelian U)).isoMk
        (@asIso _ _ _ _ ((EtaleDerived.plusAdjunction a).counit.app K.obj)
          (properPlusDerivedCounit_app_isIso a ha K)))
    (fun f ↦ properPlusCartesianCounitIso_naturality a ha f)

/-- The underlying restricted counit component is the canonical total étale derived counit. -/
theorem properPlusCartesianCounitIso_hom_app_hom (ha : IsProperHypercovering a)
    (K : DerivedCategory.Plus.CohomologyIn (EtaleCartesian.IsCartesianAbelian U)) :
    ((properPlusCartesianCounitIso a ha).hom.app K).hom =
      (EtaleDerived.plusAdjunction a).counit.app K.obj := sorry

/-- A proper hypercovering induces an equivalence between bounded-below derived
abelian étale sheaves on the base and objects with cartesian cohomology on its
total étale site, with inverse image and derived direct image as the two functors. -/
def properPlusCartesianEquivalence (ha : IsProperHypercovering a) :
    DerivedCategory.Plus (Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1}) ≌
      DerivedCategory.Plus.CohomologyIn (EtaleCartesian.IsCartesianAbelian U) :=
  CategoryTheory.Equivalence.mk
    (EtaleDerived.plusCartesianFunctor a) (EtaleDerived.plusCartesianInverse a)
    (properPlusCartesianUnitIso a ha) (properPlusCartesianCounitIso a ha)

/-- The equivalence functor is total étale derived inverse image corestricted to
cartesian cohomology. -/
theorem properPlusCartesianEquivalence_functor (ha : IsProperHypercovering a) :
    (properPlusCartesianEquivalence a ha).functor =
      EtaleDerived.plusCartesianFunctor a := sorry

/-- The inverse equivalence functor is total étale derived direct image restricted
to objects with cartesian cohomology. -/
theorem properPlusCartesianEquivalence_inverse (ha : IsProperHypercovering a) :
    (properPlusCartesianEquivalence a ha).inverse =
      EtaleDerived.plusCartesianInverse a := sorry

end AlgebraicGeometry.AlgebraicSpace.Simplicial

end
