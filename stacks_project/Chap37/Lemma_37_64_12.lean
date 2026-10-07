module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.WeaklyEtale.Normal
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 37.64.12: if `f : X ⟶ Y` is weakly étale and `Y` is normal, then `X` is normal. -/
@[stacks 0950] #check
  (AlgebraicGeometry.WeaklyEtale.isNormal :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [WeaklyEtale f], Y.isNormal → X.isNormal)
