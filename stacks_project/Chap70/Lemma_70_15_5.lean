module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.ClosedImmersion.Descent

/-!
# Lemma 70.15.5

A closed immersion of algebraic spaces that is bijective on points, together with a
closed-immersion base change, detects closed immersions under a finite-type or
finite-presentation hypothesis.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits

universe u

/- Lemma 70.15.5: Let `S` be a scheme. Let `f : X ⟶ B` and `g : B' ⟶ B` be morphisms of
algebraic spaces over `S`. Assume `g` is a closed immersion, `Points.map g : Points B' → Points B`
is bijective, `pullback.snd f g` is a closed immersion, and either `f` is of finite type or `g`
is of finite presentation. Then `f` is a closed immersion. -/
@[stacks 08B2] #check
  (AlgebraicGeometry.AlgebraicSpace.IsClosedImmersion.of_pullback_snd_of_bijective :
    ∀ {S : Scheme.{u}} {X B B' : AlgebraicSpace S}
      (f : X ⟶ B) (g : B' ⟶ B) [HasPullback f g] [IsClosedImmersion g]
      (hg_bij : Function.Bijective (Points.map g))
      [IsClosedImmersion (pullback.snd f g)]
      (hfinite : FiniteType f ∨ FinitePresentation g),
      IsClosedImmersion f)

/- If `g : B' ⟶ B` is a closed immersion that is bijective on points, the base-change
projection `pullback.snd f g` is a closed immersion, and `f` is of finite type, then `f` is a
closed immersion. -/
#check
  (AlgebraicGeometry.AlgebraicSpace.IsClosedImmersion.of_pullback_snd_of_bijective_of_finiteType :
    ∀ {S : Scheme.{u}} {X B B' : AlgebraicSpace S} (f : X ⟶ B) (g : B' ⟶ B)
      [HasPullback f g] [IsClosedImmersion g]
      (hg_bij : Function.Bijective (Points.map g))
      [IsClosedImmersion (pullback.snd f g)] [FiniteType f],
      IsClosedImmersion f)

/- If `g : B' ⟶ B` is a closed immersion that is bijective on points, the base-change
projection `pullback.snd f g` is a closed immersion, and `g` is of finite presentation, then
`f` is a closed immersion. -/
#check
  (AlgebraicGeometry.AlgebraicSpace.IsClosedImmersion.of_pullback_snd_of_bijective_of_finitePresentation :
    ∀ {S : Scheme.{u}} {X B B' : AlgebraicSpace S} (f : X ⟶ B) (g : B' ⟶ B)
      [HasPullback f g] [IsClosedImmersion g]
      (hg_bij : Function.Bijective (Points.map g))
      [IsClosedImmersion (pullback.snd f g)] [FinitePresentation g],
      IsClosedImmersion f)
