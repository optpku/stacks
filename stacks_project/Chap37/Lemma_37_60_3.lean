module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.PseudoCoherent.BaseChange
import StacksCheckRecall

open CategoryTheory CategoryTheory.Limits

universe u

/- Lemma 37.60.3: A flat base change of a pseudo-coherent morphism is pseudo-coherent. -/
@[stacks 0680] #check
  (AlgebraicGeometry.PseudoCoherent.pullback_snd :
    ∀ {X S S' : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
      [AlgebraicGeometry.PseudoCoherent f] [AlgebraicGeometry.Flat g],
      AlgebraicGeometry.PseudoCoherent (pullback.snd f g))
