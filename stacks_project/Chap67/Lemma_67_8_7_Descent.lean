/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import stacks_project.Chap67.Definition_67_5_2_Surjective
public import stacks_project.Chap67.Definition_67_8_2_QuasiCompact
public import stacks_project.Chap67.Lemma_67_6_3_UniversallyOpen

/-!
# Descent of quasi-compact morphisms of algebraic spaces

Quasi-compactness of morphisms of algebraic spaces descends along universally
open surjections. This module records the morphism-level pullback companions
for that descent.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
  CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace QuasiCompact

/-- Quasi-compactness of morphisms of algebraic spaces descends along a
universally open surjection, expressed by an `IsPullback` square. -/
theorem of_universallyOpen_surjective {S : Scheme.{u}}
    {X Y X' Y' : AlgebraicSpace S} {f : X ⟶ Y} {g : Y' ⟶ Y}
    {f' : X' ⟶ Y'} {g' : X' ⟶ X}
    [UniversallyOpen g] [Surjective g] [QuasiCompact f']
    (h : IsPullback f' g' g f) : QuasiCompact f := sorry

/-- If `g` is universally open and surjective and the base-change projection
`pullback.snd f g` is quasi-compact, then `f` is quasi-compact. -/
theorem of_pullback_snd_of_universallyOpen_surjective {S : Scheme.{u}}
    {X Y Y' : AlgebraicSpace S} (f : X ⟶ Y) (g : Y' ⟶ Y)
    [UniversallyOpen g] [Surjective g] [HasPullback f g]
    [QuasiCompact (pullback.snd f g)] : QuasiCompact f := sorry

end QuasiCompact

end AlgebraicGeometry.AlgebraicSpace
