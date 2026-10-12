/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.UniversalHomeomorphism.Cancellation
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 29.45.8 (1): the composite of two universal homeomorphisms is a universal
homeomorphism. -/
@[stacks 0H2M] #check
  (AlgebraicGeometry.UniversalHomeomorphism.comp :
    ∀ {X Y Z : AlgebraicGeometry.Scheme.{u}} {g : X ⟶ Y} {h : Y ⟶ Z},
      AlgebraicGeometry.UniversalHomeomorphism g →
        AlgebraicGeometry.UniversalHomeomorphism h →
          AlgebraicGeometry.UniversalHomeomorphism (g ≫ h))

/- Lemma 29.45.8 (2): if a composite and its left factor are universal homeomorphisms, then
its right factor is a universal homeomorphism. -/
@[stacks 0H2M] #check
  (AlgebraicGeometry.UniversalHomeomorphism.right_of_comp_left :
    ∀ {X Y Z : AlgebraicGeometry.Scheme.{u}} {g : X ⟶ Y} {h : Y ⟶ Z},
      AlgebraicGeometry.UniversalHomeomorphism (g ≫ h) →
        AlgebraicGeometry.UniversalHomeomorphism g →
          AlgebraicGeometry.UniversalHomeomorphism h)

/- Lemma 29.45.8 (3): if a composite and its right factor are universal homeomorphisms, then
its left factor is a universal homeomorphism. -/
@[stacks 0H2M] #check
  (AlgebraicGeometry.UniversalHomeomorphism.left_of_comp_right :
    ∀ {X Y Z : AlgebraicGeometry.Scheme.{u}} {g : X ⟶ Y} {h : Y ⟶ Z},
      AlgebraicGeometry.UniversalHomeomorphism (g ≫ h) →
        AlgebraicGeometry.UniversalHomeomorphism h →
          AlgebraicGeometry.UniversalHomeomorphism g)
