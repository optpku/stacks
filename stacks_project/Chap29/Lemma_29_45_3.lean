/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.UniversalHomeomorphism

/-!
# Lemma 29.45.3 compatibility entry point

Composition stability of universal homeomorphisms is owned by the neutral
scheme-morphism API in `ReasLib`.
-/

@[expose] public section

open CategoryTheory

universe u

/- Lemma 29.45.3 (0CEV): the composite of universal homeomorphisms is a
universal homeomorphism. -/
@[stacks 0CEV] #check (@AlgebraicGeometry.UniversalHomeomorphism.comp :
  ∀ {X Y Z : AlgebraicGeometry.Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z},
    AlgebraicGeometry.UniversalHomeomorphism f →
      AlgebraicGeometry.UniversalHomeomorphism g →
        AlgebraicGeometry.UniversalHomeomorphism (f ≫ g))
