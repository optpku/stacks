/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Definition_67_8_2_QuasiCompact
public import stacks_project.Chap77.Lemma_77_7_4_Limit
public import stacks_project.Chap99.«99_3_1_1»

/-!
# Lemma 99.3.6

In Situation 99.3.1, if `F` is of finite presentation and `f` is quasi-compact
and quasi-separated, then `Hom(F, G)` is limit preserving.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- Lemma 99.3.6: In Situation 99.3.1, if `F` is of finite presentation and `f`
is quasi-compact and quasi-separated, then the Hom functor `Hom(F, G)`
(`homFunctor f F G`) is limit preserving: if `T = lim T_i` is a directed limit
of affine schemes over `B`, then `Hom(F, G)(T)` is the colimit of the values at
`T_i`. -/
@[stacks 08K4]
theorem homFunctor_preservesDirectedAffineLimits
    {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B)
    [QuasiCompact f] [QuasiSeparated f] (F G : X.Modules)
    [F.IsQuasicoherent] [G.IsQuasicoherent] [F.IsFinitePresentation] :
    SchemeOver.PreservesDirectedAffineLimits B (homFunctor f F G) := sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
