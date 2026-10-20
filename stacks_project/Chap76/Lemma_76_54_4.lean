/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Thickening.Perfect
import StacksCheckRecall

/-!
# Relative perfectness along finite-order thickenings of algebraic spaces

In a cartesian square of algebraic spaces over a scheme, if `X' ⟶ Y'` is flat
and locally of finite presentation and `Y ⟶ Y'` is a finite-order thickening,
then `Y`-perfectness of `Li^* E'` implies `Y'`-perfectness of `E'`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 76.54.4: Relative perfectness descends across a finite-order thickening
in a cartesian square. The hypothesis expands `Y`-perfectness of the canonical
derived pullback into pseudo-coherence and locally finite Tor dimension over `Y`.
Flatness and local finite presentation of `f` follow by base change from `f'`. -/
@[stacks 0DL4] #check
  (AlgebraicGeometry.AlgebraicSpace.IsFiniteOrderThickening.isPerfectRelativeTo_of_pullback :
    ∀ {S : Scheme.{u}} {X X' Y Y' : AlgebraicSpace S}
      (i : X ⟶ X') (f : X ⟶ Y) (f' : X' ⟶ Y') (j : Y ⟶ Y')
      (sq : IsPullback i f f' j) [Flat f'] [LocallyOfFinitePresentation f']
      [IsFiniteOrderThickening j] (E' : ModuleDerived X'),
      (IsPseudoCoherent X ((modulePullbackDerived i).obj E') ∧
        ModuleDerived.locallyFiniteTorDimensionOver f ((modulePullbackDerived i).obj E')) →
      ModuleDerived.IsPerfectRelativeTo f' E')
