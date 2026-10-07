module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Dominant.OpenBaseChange
import StacksCheckRecall

/-!
# Lemma 29.8.5

A dominant morphism remains dominant after base change along an open morphism.

@stack 0H8F
-/

@[expose] public section

universe u

/- Lemma 29.8.5: a dominant morphism remains dominant after base change along an open
morphism. -/
@[stacks 0H8F] #check
  (AlgebraicGeometry.isDominant_pullbackSnd_of_isDominant_of_isOpenMap :
    ∀ {X S S' : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
      [AlgebraicGeometry.IsDominant f],
      IsOpenMap g.base →
        AlgebraicGeometry.IsDominant (CategoryTheory.Limits.pullback.snd f g))
