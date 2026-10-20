/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Simplicial.ProperDescent
import StacksCheckRecall

/-! # Descent of étale sheaves along proper hypercoverings -/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry Functor
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Simplicial
open scoped Simplicial

/- Lemma 85.36.2. Inverse image along a proper hypercovering is fully faithful on
étale sheaves of sets, with cartesian essential image and canonical direct image
as quasi-inverse. -/
@[stacks 0DHK] #check
  (AlgebraicGeometry.AlgebraicSpace.Simplicial.sheaf_properHypercovering_descent :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
      {U : SimplicialObject (AlgebraicSpace S)}
      (a : U ⟶ (const SimplexCategoryᵒᵖ).obj X),
      IsProperHypercovering a →
    (spacesEtaleAugmentation U a).inverseImage.Full ∧
    (spacesEtaleAugmentation U a).inverseImage.Faithful ∧
    (∀ G : Sheaf (spacesEtaleTotalTopology U) (Type (u + 1)),
      (spacesEtaleAugmentation U a).inverseImage.essImage G ↔ EtaleCartesian.IsCartesian U G) ∧
    (∀ F : Sheaf (spacesEtaleTopology X) (Type (u + 1)),
      IsIso ((spacesEtaleAugmentation U a).adjunction.unit.app F)) ∧
    (∀ G : Sheaf (spacesEtaleTotalTopology U) (Type (u + 1)),
      EtaleCartesian.IsCartesian U G →
        IsIso ((spacesEtaleAugmentation U a).adjunction.counit.app G)))

/- Lemma 85.36.2. Inverse image along a proper hypercovering is fully faithful on
étale sheaves of abelian groups, with cartesian essential image and canonical direct image
as quasi-inverse. -/
@[stacks 0DHK] #check
  (AlgebraicGeometry.AlgebraicSpace.Simplicial.abelian_properHypercovering_descent :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
      {U : SimplicialObject (AlgebraicSpace S)}
      (a : U ⟶ (const SimplexCategoryᵒᵖ).obj X),
      IsProperHypercovering a →
    (spacesEtaleAugmentation U a).abelianInverseImage.Full ∧
    (spacesEtaleAugmentation U a).abelianInverseImage.Faithful ∧
    (∀ G : Sheaf (spacesEtaleTotalTopology U) AddCommGrpCat.{u + 1},
      (spacesEtaleAugmentation U a).abelianInverseImage.essImage G ↔
        EtaleCartesian.IsCartesianAbelian U G) ∧
    (∀ F : Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1},
      IsIso ((spacesEtaleAugmentation U a).abelianAdjunction.unit.app F)) ∧
    (∀ G : Sheaf (spacesEtaleTotalTopology U) AddCommGrpCat.{u + 1},
      EtaleCartesian.IsCartesianAbelian U G →
        IsIso ((spacesEtaleAugmentation U a).abelianAdjunction.counit.app G)))

