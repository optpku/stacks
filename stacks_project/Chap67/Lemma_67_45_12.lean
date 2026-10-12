/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Lemma_67_45_12_Cancellation
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 67.45.12 (1): if `f ≫ g` is finite and `g` is separated then `f` is
finite. -/
@[stacks 081Z] #check
  (IsFinite.of_comp :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z)
      [IsFinite (f ≫ g)] [Separated g],
      IsFinite f)

/- Lemma 67.45.12 (2): if `f ≫ g` is integral and `g` is separated then `f` is
integral. -/
@[stacks 081Z] #check
  (IsIntegralHom.of_comp :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z)
      [IsIntegralHom (f ≫ g)] [Separated g],
      IsIntegralHom f)
