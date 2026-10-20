module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiCompact.DominantBaseChange
import StacksCheckRecall

/-!
# Lemma 29.8.4

Dominance after base change along a morphism that lifts generalizations.

@stack 0H3F
-/

@[expose] public section

universe u

/- Lemma 29.8.4
A quasi-compact dominant morphism of schemes remains dominant after base change along a
morphism whose underlying map lifts generalizations.
-/
@[stacks 0H3F] #check
  (AlgebraicGeometry.isDominant_pullbackSnd_of_isDominant_of_generalizingMap :
    ∀ {X S S' : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
        [AlgebraicGeometry.QuasiCompact f] [AlgebraicGeometry.IsDominant f],
      GeneralizingMap g.base →
        AlgebraicGeometry.IsDominant (CategoryTheory.Limits.pullback.snd f g))
