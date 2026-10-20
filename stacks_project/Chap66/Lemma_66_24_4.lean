module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleLocalRing.Noetherian
public import stacks_project.Chap66.Definition_66_22_2_EtaleLocalRing
public import stacks_project.Chap66.Definition_66_24_1_Noetherian
import StacksCheckRecall

/-!
# Étale local rings of Noetherian algebraic spaces

The étale-site stalk of a locally Noetherian algebraic space at a geometric point is a
Noetherian local ring.
-/

universe u

/- Lemma 66.24.4: The étale local ring of a Noetherian algebraic space at a geometric
point is a Noetherian local ring. -/
@[stacks 08AH] #check
  (AlgebraicGeometry.AlgebraicSpace.etaleLocalRing.isNoetherianLocalRing :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {X : AlgebraicGeometry.AlgebraicSpace S}
      [AlgebraicGeometry.AlgebraicSpace.IsNoetherian X]
      (xbar : AlgebraicGeometry.AlgebraicSpace.GeometricPoint X),
      IsNoetherianRing (AlgebraicGeometry.AlgebraicSpace.etaleLocalRing X xbar) ∧
        IsLocalRing (AlgebraicGeometry.AlgebraicSpace.etaleLocalRing X xbar))
