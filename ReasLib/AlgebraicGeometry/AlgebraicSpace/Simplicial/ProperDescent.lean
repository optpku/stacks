/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Simplicial.ProperHypercovering
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Simplicial.EtaleCartesian
public import ReasLib.CategoryTheory.Sites.Topos.Abelian
public import Mathlib.CategoryTheory.EssentialImage

/-! # Descent of étale sheaves along proper hypercoverings -/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry Functor
open scoped Simplicial

namespace AlgebraicGeometry.AlgebraicSpace.Simplicial

variable {S : Scheme.{u}} {X : AlgebraicSpace S}
variable {U : SimplicialObject (AlgebraicSpace S)}
variable (a : U ⟶ (const SimplexCategoryᵒᵖ).obj X)

/-- Inverse image along a proper hypercovering is fully faithful on étale sheaves of sets,
with cartesian essential image; its adjunction unit and its counit on cartesian sheaves
are invertible. -/
theorem sheaf_properHypercovering_descent (ha : IsProperHypercovering a) :
    (spacesEtaleAugmentation U a).inverseImage.Full ∧
    (spacesEtaleAugmentation U a).inverseImage.Faithful ∧
    (∀ G : Sheaf (spacesEtaleTotalTopology U) (Type (u + 1)),
      (spacesEtaleAugmentation U a).inverseImage.essImage G ↔ EtaleCartesian.IsCartesian U G) ∧
    (∀ F : Sheaf (spacesEtaleTopology X) (Type (u + 1)),
      IsIso ((spacesEtaleAugmentation U a).adjunction.unit.app F)) ∧
    (∀ G : Sheaf (spacesEtaleTotalTopology U) (Type (u + 1)),
      EtaleCartesian.IsCartesian U G →
        IsIso ((spacesEtaleAugmentation U a).adjunction.counit.app G)) := sorry

/-- A total étale sheaf of sets descends along a proper hypercovering exactly when it is cartesian. -/
theorem properSheaf_mem_essImage_iff_isCartesian (ha : IsProperHypercovering a)
    (G : Sheaf (spacesEtaleTotalTopology U) (Type (u + 1))) :
    (spacesEtaleAugmentation U a).inverseImage.essImage G ↔ EtaleCartesian.IsCartesian U G :=
  (sheaf_properHypercovering_descent a ha).2.2.1 G

/-- Inverse image along a proper hypercovering is fully faithful on abelian étale sheaves,
with cartesian essential image; its adjunction unit and its counit on cartesian sheaves
are invertible. -/
theorem abelian_properHypercovering_descent (ha : IsProperHypercovering a) :
    (spacesEtaleAugmentation U a).abelianInverseImage.Full ∧
    (spacesEtaleAugmentation U a).abelianInverseImage.Faithful ∧
    (∀ G : Sheaf (spacesEtaleTotalTopology U) AddCommGrpCat.{u + 1},
      (spacesEtaleAugmentation U a).abelianInverseImage.essImage G ↔
        EtaleCartesian.IsCartesianAbelian U G) ∧
    (∀ F : Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1},
      IsIso ((spacesEtaleAugmentation U a).abelianAdjunction.unit.app F)) ∧
    (∀ G : Sheaf (spacesEtaleTotalTopology U) AddCommGrpCat.{u + 1},
      EtaleCartesian.IsCartesianAbelian U G →
        IsIso ((spacesEtaleAugmentation U a).abelianAdjunction.counit.app G)) := sorry

/-- An abelian total étale sheaf descends along a proper hypercovering exactly when it is cartesian. -/
theorem properAbelian_mem_essImage_iff_isCartesian (ha : IsProperHypercovering a)
    (G : Sheaf (spacesEtaleTotalTopology U) AddCommGrpCat.{u + 1}) :
    (spacesEtaleAugmentation U a).abelianInverseImage.essImage G ↔
      EtaleCartesian.IsCartesianAbelian U G :=
  (abelian_properHypercovering_descent a ha).2.2.1 G

end AlgebraicGeometry.AlgebraicSpace.Simplicial
