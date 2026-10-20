/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Definition_67_8_2_QuasiCompact
public import stacks_project.Chap77.Lemma_77_7_4_Limit
public import stacks_project.Chap99.«99_7_1_2_Functor»

/-!
# Lemma 99.7.7

In Situation 99.7.1, if `f` is quasi-compact and quasi-separated and `F` is of
finite presentation, then `Q^{fp}_{F/X/B}` preserves directed inverse limits of
affine schemes over `B`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Quot

/-- Lemma 99.7.7: In Situation 99.7.1, assume also that `f` is quasi-compact and
quasi-separated and that `F` is of finite presentation. Then the functor
`Q^{fp}_{F/X/B}` (`fpFunctor f F`) preserves directed inverse limits of affine
schemes over `B`: if `T = lim T_i` is a directed limit of affine schemes over
`B`, then `Q^{fp}_{F/X/B}(T)` is the colimit of the values at `T_i`. -/
@[stacks 082Q]
theorem fpFunctor_preservesDirectedAffineLimits
    {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B)
    [QuasiCompact f] [QuasiSeparated f] (F : X.Modules)
    [F.IsQuasicoherent] [F.IsFinitePresentation] :
    SchemeOver.PreservesDirectedAffineLimits B (fpFunctor f F) := sorry

end AlgebraicGeometry.AlgebraicSpace.Quot
