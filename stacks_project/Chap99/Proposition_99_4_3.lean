module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import stacks_project.Chap67.Lemma_67_28_8_FinitePresentation
public import stacks_project.Chap67.Lemma_67_31_3_FlatOver
public import stacks_project.Chap67.Lemma_67_31_6_ModuleSupport
public import stacks_project.Chap75.Lemma_75_7_3_ProperOver
public import stacks_project.Chap99.Lemma_99_3_8_Yoneda
public import stacks_project.Chap99.Lemma_99_4_1_Functor

/-!
# Proposition 99.4.3

In Situation 99.3.1, if `f` is of finite presentation and `F` and `G` are
finitely presented `𝒪_X`-modules, flat over `B`, with support proper over `B`,
then the functor `Isom(F, G)` is an algebraic space affine of finite
presentation over `B`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- Proposition 99.4.3: In Situation 99.3.1, if `f` is of finite presentation
and `F` and `G` are finitely presented `𝒪_X`-modules, flat over `B`, with
support proper over `B`, then the functor `Isom(F, G)` is an algebraic space
affine of finite presentation over `B`. -/
@[stacks 08K9]
theorem isomFunctor_isAffineFinitePresentationOver
    {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B) [FinitePresentation f]
    (F G : X.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent]
    [F.IsFinitePresentation] [G.IsFinitePresentation]
    (hF_flat : flatOver F f) (hG_flat : flatOver G f)
    (hF_support : ClosedSubset.IsProperOver f (Closeds.closure (moduleSupport F)))
    (hG_support : ClosedSubset.IsProperOver f (Closeds.closure (moduleSupport G))) :
    IsAffineFinitePresentationOver (isomFunctor f F G) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
