module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Simplicial.FppfDescent
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry Functor
open scoped Simplicial
open AlgebraicGeometry.AlgebraicSpace AlgebraicGeometry.AlgebraicSpace.Simplicial

/- Lemma 85.33.2: Sheaves of sets. For an fppf hypercovering, augmentation inverse image is fully
faithful with cartesian essential image and quasi-inverse given by augmentation direct image. -/
@[stacks 0DH6] #check (AlgebraicGeometry.AlgebraicSpace.Simplicial.sheaf_fppfHypercovering_descent :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {U : SimplicialObject (AlgebraicSpace S)}
    (a : U ⟶ (const SimplexCategoryᵒᵖ).obj X) (ha : IsFppfHypercovering a),
    (spacesEtaleAugmentation U a).inverseImage.Full ∧
    (spacesEtaleAugmentation U a).inverseImage.Faithful ∧
    (∀ G : Sheaf (spacesEtaleTotalTopology U) (Type (u + 1)),
      (spacesEtaleAugmentation U a).inverseImage.essImage G ↔ EtaleCartesian.IsCartesian U G) ∧
    (∀ F : Sheaf (spacesEtaleTopology X) (Type (u + 1)),
      IsIso ((spacesEtaleAugmentation U a).adjunction.unit.app F)) ∧
    (∀ G : Sheaf (spacesEtaleTotalTopology U) (Type (u + 1)),
      EtaleCartesian.IsCartesian U G →
        IsIso ((spacesEtaleAugmentation U a).adjunction.counit.app G)))

/- Lemma 85.33.2: Abelian sheaves. For an fppf hypercovering, augmentation inverse image is fully
faithful with cartesian essential image and quasi-inverse given by augmentation direct image. -/
@[stacks 0DH6] #check (AlgebraicGeometry.AlgebraicSpace.Simplicial.abelian_fppfHypercovering_descent :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {U : SimplicialObject (AlgebraicSpace S)}
    (a : U ⟶ (const SimplexCategoryᵒᵖ).obj X) (ha : IsFppfHypercovering a),
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

