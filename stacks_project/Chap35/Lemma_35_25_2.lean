module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.OpenImmersion
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 35.25.2: A universally injective étale morphism is an open immersion. -/
@[stacks 02LC] #check
  (AlgebraicGeometry.IsOpenImmersion.of_etale_of_universallyInjective :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
      [AlgebraicGeometry.Etale f] [AlgebraicGeometry.UniversallyInjective f],
      AlgebraicGeometry.IsOpenImmersion f)
