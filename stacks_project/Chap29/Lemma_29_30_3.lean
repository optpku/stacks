/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic.Stability
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/-!
# Lemma 29.30.3

This chapter entry is a compatibility facade for composition stability of
syntomic scheme morphisms.
-/

/- Lemma 29.30.3: the composition of syntomic morphisms is syntomic. -/
@[stacks 01UH] #check (AlgebraicGeometry.syntomic_comp :
  ∀ {X Y Z : AlgebraicGeometry.Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z},
    AlgebraicGeometry.Syntomic f → AlgebraicGeometry.Syntomic g →
      AlgebraicGeometry.Syntomic (f ≫ g))
