module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Simplicial.FppfHypercovering
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Simplicial.EtaleCartesian
public import ReasLib.CategoryTheory.Sites.Topos.Abelian

/-! # Descent of étale sheaves along fppf hypercoverings -/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry Functor
open scoped Simplicial

namespace AlgebraicGeometry.AlgebraicSpace.Simplicial

variable {S : Scheme.{u}} {X : AlgebraicSpace S}
variable {U : SimplicialObject (AlgebraicSpace S)}
variable (a : U ⟶ (const SimplexCategoryᵒᵖ).obj X)

/-- Inverse image along an fppf hypercovering is fully faithful on étale sheaves of sets,
with cartesian essential image; its adjunction unit and its counit on cartesian sheaves
are invertible. -/
theorem sheaf_fppfHypercovering_descent (ha : IsFppfHypercovering a) :
    (spacesEtaleAugmentation U a).inverseImage.Full ∧
    (spacesEtaleAugmentation U a).inverseImage.Faithful ∧
    (∀ G : Sheaf (spacesEtaleTotalTopology U) (Type (u + 1)),
      (spacesEtaleAugmentation U a).inverseImage.essImage G ↔ EtaleCartesian.IsCartesian U G) ∧
    (∀ F : Sheaf (spacesEtaleTopology X) (Type (u + 1)),
      IsIso ((spacesEtaleAugmentation U a).adjunction.unit.app F)) ∧
    (∀ G : Sheaf (spacesEtaleTotalTopology U) (Type (u + 1)),
      EtaleCartesian.IsCartesian U G →
        IsIso ((spacesEtaleAugmentation U a).adjunction.counit.app G)) := sorry

/-- A total étale sheaf of sets descends along an fppf hypercovering exactly when it is cartesian. -/
theorem sheaf_mem_essImage_iff_isCartesian (ha : IsFppfHypercovering a)
    (G : Sheaf (spacesEtaleTotalTopology U) (Type (u + 1))) :
    (spacesEtaleAugmentation U a).inverseImage.essImage G ↔ EtaleCartesian.IsCartesian U G :=
  (sheaf_fppfHypercovering_descent a ha).2.2.1 G

/-- Inverse image along an fppf hypercovering is fully faithful on abelian étale sheaves,
with cartesian essential image; its adjunction unit and its counit on cartesian sheaves
are invertible. -/
theorem abelian_fppfHypercovering_descent (ha : IsFppfHypercovering a) :
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

/-- An abelian total étale sheaf descends along an fppf hypercovering exactly when it is cartesian. -/
theorem abelian_mem_essImage_iff_isCartesian (ha : IsFppfHypercovering a)
    (G : Sheaf (spacesEtaleTotalTopology U) AddCommGrpCat.{u + 1}) :
    (spacesEtaleAugmentation U a).abelianInverseImage.essImage G ↔
      EtaleCartesian.IsCartesianAbelian U G :=
  (abelian_fppfHypercovering_descent a ha).2.2.1 G

end AlgebraicGeometry.AlgebraicSpace.Simplicial
