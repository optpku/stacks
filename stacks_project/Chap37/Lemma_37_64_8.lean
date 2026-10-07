module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.WeaklyEtale.FormallyUnramified
import StacksCheckRecall

open CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 37.64.8: a weakly étale morphism of schemes is formally unramified. -/
@[stacks 094W] #check
  (AlgebraicGeometry.WeaklyEtale.instFormallyUnramified :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
      [AlgebraicGeometry.WeaklyEtale f], AlgebraicGeometry.FormallyUnramified f)

#check
  (AlgebraicGeometry.WeaklyEtale.isZero_relativeDifferentials :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
      [AlgebraicGeometry.WeaklyEtale f],
        CategoryTheory.Limits.IsZero (Ω[f.toShHom]))
