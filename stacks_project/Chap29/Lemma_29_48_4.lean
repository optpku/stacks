module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteLocallyFree.Operations
import StacksCheckRecall

@[expose] public section

universe u

/-!
# Lemma 29.48.4

The reusable base-change API is maintained in
`ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteLocallyFree.Operations`.
-/

/- Lemma 29.48.4: finite locally free scheme morphisms are stable under arbitrary base change. -/
@[stacks 02KD] #check
  (AlgebraicGeometry.IsFiniteLocallyFree.pullback_snd :
    ∀ {X S S' : AlgebraicGeometry.Scheme.{u}}
      (f : X ⟶ S) (g : S' ⟶ S),
      AlgebraicGeometry.IsFiniteLocallyFree f →
        AlgebraicGeometry.IsFiniteLocallyFree (CategoryTheory.Limits.pullback.snd f g))
