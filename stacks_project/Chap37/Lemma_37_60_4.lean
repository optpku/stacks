/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.PseudoCoherent.Composition
import StacksCheckRecall

open CategoryTheory

universe u

/- Lemma 37.60.4: A composition of pseudo-coherent morphisms of schemes is pseudo-coherent. -/
@[stacks 0681] #check (AlgebraicGeometry.PseudoCoherent.comp :
  ∀ {X Y Z : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [AlgebraicGeometry.PseudoCoherent f] [AlgebraicGeometry.PseudoCoherent g],
    AlgebraicGeometry.PseudoCoherent (f ≫ g))
