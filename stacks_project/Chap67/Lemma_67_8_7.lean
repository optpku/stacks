/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.MorphismProperty.Descent
public import stacks_project.Chap67.Lemma_67_8_7_Descent

/-!
# Descent of quasi-compact morphisms of algebraic spaces

Quasi-compactness of morphisms of algebraic spaces descends along universally
open surjections.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 67.8.7: Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme
`S`, and let `g : Y' ⟶ Y` be universally open and surjective. If a base change of
`f` along `g` is quasi-compact, then `f` is quasi-compact. -/
@[stacks 04ZJ]
instance quasiCompact_descendsAlong_universallyOpen_inf_surjective {S : Scheme.{u}} :
    MorphismProperty.DescendsAlong
      (@QuasiCompact S : MorphismProperty (AlgebraicSpace S))
      ((@UniversallyOpen S : MorphismProperty (AlgebraicSpace S)) ⊓
        (@Surjective S : MorphismProperty (AlgebraicSpace S))) := sorry

#check QuasiCompact.of_universallyOpen_surjective
#check QuasiCompact.of_pullback_snd_of_universallyOpen_surjective

end AlgebraicGeometry.AlgebraicSpace
