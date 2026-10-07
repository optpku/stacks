module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.WeaklyEtale.UniversalHomeomorphism
import StacksCheckRecall

open CategoryTheory

universe u

/- Lemma 37.64.14: a weakly étale universal homeomorphism of schemes is an isomorphism. -/
@[stacks 0F6V] #check
  (AlgebraicGeometry.WeaklyEtale.instIsIsoOfUniversalHomeomorphism :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
      [AlgebraicGeometry.WeaklyEtale f] [AlgebraicGeometry.UniversalHomeomorphism f],
        IsIso f)
