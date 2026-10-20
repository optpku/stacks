module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.RestrictionTopos
import StacksCheckRecall

/-! # Étale restriction and inverse image on the source small site

@stack 03LP
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 66.18.11. Étale postcomposition is cocontinuous and continuous, induces the canonical
small étale morphism of topoi, and computes inverse-image sections by restriction. -/
@[stacks 03LP]
#check (AlgebraicGeometry.AlgebraicSpace.etaleRestriction_isCocontinuous :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [AlgebraicSpace.Etale f],
    (AlgebraicSpace.etaleRestriction f).IsCocontinuous
      (AlgebraicSpace.smallEtaleTopology X) (AlgebraicSpace.smallEtaleTopology Y))

#check (AlgebraicGeometry.AlgebraicSpace.smallEtaleMorphismOfTopoi_sheafPullbackCocontinuous :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [AlgebraicSpace.Etale f],
    (AlgebraicSpace.smallEtaleMorphismOfTopoi f).inverseImage ≅
      (AlgebraicSpace.etaleRestriction f).sheafPullbackCocontinuous (Type (u + 1))
        (AlgebraicSpace.smallEtaleTopology X) (AlgebraicSpace.smallEtaleTopology Y))

#check (AlgebraicGeometry.AlgebraicSpace.etaleRestriction_isContinuous :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [AlgebraicSpace.Etale f],
    (AlgebraicSpace.etaleRestriction f).IsContinuous
      (AlgebraicSpace.smallEtaleTopology X) (AlgebraicSpace.smallEtaleTopology Y))

#check (AlgebraicGeometry.AlgebraicSpace.smallEtaleMorphismOfTopoi_inverseImage_obj :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [AlgebraicSpace.Etale f]
    (G : Sheaf (AlgebraicSpace.smallEtaleTopology Y) (Type (u + 1)))
    (U : AlgebraicSpace.smallEtaleSite X),
    ((AlgebraicSpace.smallEtaleMorphismOfTopoi f).inverseImage.obj G).obj.obj (Opposite.op U) ≅
      G.obj.obj (Opposite.op ((AlgebraicSpace.etaleRestriction f).obj U)))
