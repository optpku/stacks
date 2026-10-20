module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Ample
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 29.43.6: let `f : X ⟶ S` be a proper morphism of schemes. If there exists an
`f`-ample invertible module on `X`, then `f` is locally projective. -/
@[stacks 0B5N] #check
  (AlgebraicGeometry.locallyProjective_of_isProper_exists_relativelyAmple :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S),
      [AlgebraicGeometry.IsProper f] →
        (∃ L : X.Modules, AlgebraicGeometry.RelativelyAmple f L) →
          AlgebraicGeometry.LocallyProjective f)
