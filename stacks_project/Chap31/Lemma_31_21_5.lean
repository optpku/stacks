/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RegularImmersion.QuasiRegularCriterion
import StacksCheckRecall

@[expose] public section

universe u

#check (AlgebraicGeometry.IsQuasiRegularImmersion.conormalCriterion :
  ∀ {X Z : AlgebraicGeometry.Scheme.{u}} (i : Z ⟶ X)
    [AlgebraicGeometry.IsImmersion i], Prop)

/- Lemma 31.21.5: an immersion of schemes is quasi-regular if and only if it is locally of
finite presentation, its conormal sheaf is finite locally free, and its canonical conormal map
to the associated graded algebra is an isomorphism. -/
@[stacks 063M] #check
  (AlgebraicGeometry.IsQuasiRegularImmersion.iff_locallyOfFinitePresentation_and_conormalCriterion :
    ∀ {X Z : AlgebraicGeometry.Scheme.{u}} (i : Z ⟶ X)
      [AlgebraicGeometry.IsImmersion i],
      AlgebraicGeometry.IsQuasiRegularImmersion i ↔
        AlgebraicGeometry.LocallyOfFinitePresentation i ∧
          AlgebraicGeometry.IsQuasiRegularImmersion.conormalCriterion i)
