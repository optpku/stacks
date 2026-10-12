/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Lemma_67_31_3_FlatOver
public import stacks_project.Chap67.Lemma_67_31_6_ModuleSupport
public import stacks_project.Chap75.Lemma_75_7_3_ProperOver
public import stacks_project.Chap99.«99_3_1_1»
public import stacks_project.Chap99.Lemma_99_3_8_Yoneda

/-!
# Lemma 99.3.9

In Situation 99.3.1, if `B` is Noetherian, `f` is locally of finite type and
quasi-separated, `F` is of finite type, and `G` is of finite type, flat over
`B`, with support proper over `B`, then `Hom(F, G)` is an algebraic space
affine of finite presentation over `B`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- Lemma 99.3.9: In Situation 99.3.1, if `B` is a Noetherian algebraic space,
`f` is locally of finite type and quasi-separated, `F` is a finite type
`𝒪_X`-module, and `G` is a finite type `𝒪_X`-module, flat over `B`, with
support proper over `B`, then the functor `Hom(F, G)` is an algebraic space
affine of finite presentation over `B`. -/
@[stacks 08JY]
theorem homFunctor_isAffineFinitePresentation
    {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B)
    [LocallyOfFiniteType f] [QuasiSeparated f] [IsNoetherian B]
    (F G : X.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent]
    [F.IsFiniteType] [G.IsFiniteType] (hG_flat : flatOver G f)
    (hG_support : ClosedSubset.IsProperOver f (Closeds.closure (moduleSupport G))) :
    IsAffineFinitePresentationOver (homFunctor f F G) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
