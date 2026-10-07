module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import stacks_project.Chap67.Lemma_67_28_8_FinitePresentation
public import stacks_project.Chap67.Lemma_67_31_3_FlatOver
public import stacks_project.Chap67.Lemma_67_31_6_ModuleSupport
public import stacks_project.Chap75.Lemma_75_7_3_ProperOver
public import stacks_project.Chap99.«99_3_1_1»
public import stacks_project.Chap99.Proposition_99_3_10_Representable

/-!
# Proposition 99.3.10

In Situation 99.3.1, if `f` is of finite presentation and `G` is a finitely
presented `𝒪_X`-module, flat over `B`, with support proper over `B`, then
`Hom(F, G)` is an algebraic space affine over `B`. If also `F` is of finite
presentation, then `Hom(F, G)` is of finite presentation over `B`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- Proposition 99.3.10 (1): In Situation 99.3.1, if `f` is of finite
presentation and `G` is a finitely presented `𝒪_X`-module, flat over `B`, with
support proper over `B`, then the functor `Hom(F, G)` is an algebraic space
affine over `B`. -/
@[stacks 08K6]
theorem homFunctor_isAffineOver
    {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B) [FinitePresentation f]
    (F G : X.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent] [G.IsFinitePresentation]
    (hG_flat : flatOver G f)
    (hG_support : ClosedSubset.IsProperOver f (Closeds.closure (moduleSupport G))) :
    IsAffineOver (homFunctor f F G) :=
  sorry

/-- Proposition 99.3.10 (2): In Situation 99.3.1, under the hypotheses of
clause (1), if also `F` is of finite presentation, then the functor
`Hom(F, G)` is of finite presentation over `B`. -/
@[stacks 08K6]
theorem homFunctor_isFinitePresentationOver
    {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B) [FinitePresentation f]
    (F G : X.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent]
    [F.IsFinitePresentation] [G.IsFinitePresentation]
    (hG_flat : flatOver G f)
    (hG_support : ClosedSubset.IsProperOver f (Closeds.closure (moduleSupport G))) :
    IsFinitePresentationOver (homFunctor f F G) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
