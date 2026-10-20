/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation

/-!
# Descent of closed immersions of algebraic spaces

Closed immersions descend along point-bijective closed immersions under a finite-type or
finite-presentation hypothesis.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace IsClosedImmersion

/-- Let `f : X ⟶ B` and `g : B' ⟶ B` be morphisms of algebraic spaces over a scheme.
If `g` is a closed immersion bijective on points, `pullback.snd f g` is a closed immersion,
and either `f` is of finite type or `g` is of finite presentation, then `f` is a closed
immersion. -/
theorem of_pullback_snd_of_bijective {S : Scheme.{u}} {X B B' : AlgebraicSpace S}
    (f : X ⟶ B) (g : B' ⟶ B) [HasPullback f g] [IsClosedImmersion g]
    (hg_bij : Function.Bijective (Points.map g))
    [IsClosedImmersion (pullback.snd f g)]
    (hfinite : FiniteType f ∨ FinitePresentation g) :
    IsClosedImmersion f :=
  sorry

/-- If `g : B' ⟶ B` is a closed immersion that is bijective on points, the base-change
projection `pullback.snd f g` is a closed immersion, and `f` is of finite type, then `f` is a
closed immersion. -/
theorem of_pullback_snd_of_bijective_of_finiteType {S : Scheme.{u}}
    {X B B' : AlgebraicSpace S} (f : X ⟶ B) (g : B' ⟶ B)
    [HasPullback f g] [IsClosedImmersion g]
    (hg_bij : Function.Bijective (Points.map g))
    [IsClosedImmersion (pullback.snd f g)] [FiniteType f] :
    IsClosedImmersion f :=
  of_pullback_snd_of_bijective f g hg_bij (Or.inl inferInstance)

/-- If `g : B' ⟶ B` is a closed immersion that is bijective on points, the base-change
projection `pullback.snd f g` is a closed immersion, and `g` is of finite presentation, then
`f` is a closed immersion. -/
theorem of_pullback_snd_of_bijective_of_finitePresentation {S : Scheme.{u}}
    {X B B' : AlgebraicSpace S} (f : X ⟶ B) (g : B' ⟶ B)
    [HasPullback f g] [IsClosedImmersion g]
    (hg_bij : Function.Bijective (Points.map g))
    [IsClosedImmersion (pullback.snd f g)] [FinitePresentation g] :
    IsClosedImmersion f :=
  of_pullback_snd_of_bijective f g hg_bij (Or.inr inferInstance)

end IsClosedImmersion

end AlgebraicGeometry.AlgebraicSpace
