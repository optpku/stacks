/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap65.Lemma_65_12_4_Immersion
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Lemma_67_28_8_FinitePresentation

/-!
# Lemma 70.15.5

A closed immersion of algebraic spaces that is bijective on points, together with a
closed-immersion base change, detects closed immersions under a finite-type or
finite-presentation hypothesis.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace IsClosedImmersion

/-- Lemma 70.15.5: Let `S` be a scheme. Let `f : X ⟶ B` and `g : B' ⟶ B` be morphisms of
algebraic spaces over `S`. Assume `g` is a closed immersion, `Points.map g : Points B' → Points B`
is bijective, `pullback.snd f g` is a closed immersion, and either `f` is of finite type or `g`
is of finite presentation. Then `f` is a closed immersion. -/
@[stacks 08B2]
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
  sorry

/-- If `g : B' ⟶ B` is a closed immersion that is bijective on points, the base-change
projection `pullback.snd f g` is a closed immersion, and `g` is of finite presentation, then
`f` is a closed immersion. -/
theorem of_pullback_snd_of_bijective_of_finitePresentation {S : Scheme.{u}}
    {X B B' : AlgebraicSpace S} (f : X ⟶ B) (g : B' ⟶ B)
    [HasPullback f g] [IsClosedImmersion g]
    (hg_bij : Function.Bijective (Points.map g))
    [IsClosedImmersion (pullback.snd f g)] [FinitePresentation g] :
    IsClosedImmersion f :=
  sorry

end IsClosedImmersion

end AlgebraicGeometry.AlgebraicSpace
