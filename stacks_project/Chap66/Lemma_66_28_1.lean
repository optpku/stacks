module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RingedSite.LocalHom
import StacksCheckRecall

/-!
# Lemma 66.28.1

The morphism of small étale ringed topoi associated to a morphism of algebraic spaces is a
morphism of locally ringed topoi in the sense of Modules on Sites, Definition 18.40.9.
-/

open CategoryTheory

universe u

/- Lemma 66.28.1: the morphism of small étale ringed topoi associated to a morphism
of algebraic spaces over a scheme is a morphism of locally ringed topoi. -/
@[stacks 04KJ] #check (AlgebraicGeometry.AlgebraicSpace.commInverseImageStructureSheafMap_isLocal :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X Y : AlgebraicGeometry.AlgebraicSpace S}
    (f : X ⟶ Y),
    CategoryTheory.Sheaf.LocalHom.IsLocal
      (AlgebraicGeometry.AlgebraicSpace.commInverseImageStructureSheafMap f))
