/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.OpenFiniteEtale
public import ReasLib.AlgebraicGeometry.Scheme.Etale.CubicCover
import StacksCheckRecall

/-!
# Lemma [Stacks 0HAR]

The étale cover obtained by deleting the ramified point of a cubic cover of a
smooth connected affine complex curve cannot be refined by any finite
composition of open immersions and finite étale morphisms.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

/- Lemma [Stacks 0HAR]
The étale cover `U ⟶ X` cannot be refined by any finite composition of open immersions
and finite étale morphisms. -/
@[stacks 0HAR] #check (AlgebraicGeometry.CubicEtaleCover.not_exists_pointedRefinement :
  ∀ c : AlgebraicGeometry.CubicEtaleCover, ¬ c.HasPointedRefinement)

#check (AlgebraicGeometry.CubicEtaleCover.not_exists_surjective_factorization :
  ∀ c : AlgebraicGeometry.CubicEtaleCover,
    ¬ ∃ (W : Scheme.{0}) (h : W ⟶ c.X.left) (lift : W ⟶ c.U.toScheme),
      AlgebraicGeometry.openImmersionOrFiniteEtale.multiplicativeClosure h ∧
        AlgebraicGeometry.Surjective h ∧ lift ≫ c.f = h)
