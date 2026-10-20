/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.Bounded
public import stacks_project.Chap67.Lemma_67_28_8_FinitePresentation
public import stacks_project.Chap67.Lemma_67_31_6_ModuleSupport
public import stacks_project.Chap75.Definition_75_5_1_DerivedQCoh
public import stacks_project.Chap75.Definition_75_14_1_PerfectApproximation
public import stacks_project.Chap75.Lemma_75_3_1_Pushforward
public import stacks_project.Chap75.Lemma_75_7_3_ProperOver
public import stacks_project.Chap75.Lemma_75_21_4_Comparison
public import stacks_project.Chap77.Theorem_77_4_7_FlatOver

/-!
# Perfect derived pushforward of a tensor with a bounded relatively flat finitely presented complex

Along a morphism of finite presentation of algebraic spaces, the derived pushforward of the
derived tensor of a perfect object with a bounded complex of finitely presented modules that
are flat over the target with support proper over the target is perfect, and its formation
commutes with arbitrary base change.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory Limits
open CategoryTheory.DerivedCategory CategoryTheory.DerivedCategory.DerivedTensor
open CategoryTheory.MonoidalCategory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- Lemma 75.25.1 (1): let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of finite
presentation between algebraic spaces over `S`. Let `E` be a perfect object of `D(𝒪_X)`,
and let `G` be a bounded complex of finitely presented `𝒪_X`-modules, flat over `Y`,
with support proper over `Y`. Then
`K = (Modules.pushforwardDerived f).obj (DerivedTensor.Right.obj E (DerivedCategory.Q.obj G))`
is a perfect object of `D(𝒪_Y)`. -/
@[stacks 0A1P]
theorem pushforwardDerived_tensor_isPerfect_of_finitePresentation
    (f : X ⟶ Y) [FinitePresentation f] (E : ModuleDerived X) (hE : IsPerfect E)
    (G : CochainComplex (Modules X) ℤ)
    (hG_bounded : CochainComplex.bounded (Modules X) G)
    (hG_fp : ∀ i : ℤ, (G.X i).IsFinitePresentation)
    (hG_flat : ∀ i : ℤ, ∀ x, Modules.flatOverAt (G.X i) f x)
    (hG_support : ∀ i : ℤ, ClosedSubset.IsProperOver f
      (Closeds.closure (Modules.moduleSupport (G.X i)))) :
    IsPerfect ((Modules.pushforwardDerived f).obj
      (DerivedTensor.Right.obj E (DerivedCategory.Q.obj G))) := sorry

/-- Lemma 75.25.1 (2): under the same hypotheses, formation of
`K = Rf_*(E ⊗^L Q(G))` commutes with arbitrary base change: for every cartesian square,
the comparison `Lg^* Rf_*(E ⊗^L Q(G)) ⟶ Rf'_*(L(g')^* E ⊗^L Q((g')^* G))` is an
isomorphism, using ordinary termwise pullback of `G` on the right. -/
@[stacks 0A1P]
theorem pushforwardDerived_tensor_baseChange_isIso_of_finitePresentation
    (f : X ⟶ Y) [FinitePresentation f] (E : ModuleDerived X) (hE : IsPerfect E)
    (G : CochainComplex (Modules X) ℤ)
    (hG_bounded : CochainComplex.bounded (Modules X) G)
    (hG_fp : ∀ i : ℤ, (G.X i).IsFinitePresentation)
    (hG_flat : ∀ i : ℤ, ∀ x, Modules.flatOverAt (G.X i) f x)
    (hG_support : ∀ i : ℤ, ClosedSubset.IsProperOver f
      (Closeds.closure (Modules.moduleSupport (G.X i))))
    {X' Y' : AlgebraicSpace S}
    [MonoidalCategory (ModuleDerived X)] [MonoidalCategory (ModuleDerived X')]
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y)
    [(ModuleDerived.pullback g').Monoidal]
    [IsIso (ModuleDerived.pullbackCompComparison f' g)]
    [IsIso (ModuleDerived.pullbackCompComparison g' f)]
    (sq : IsPullback g' f' f g)
    (T_X : @Right.Monoidal.Model (Modules X) _ _ _ _ _ _ _)
    (T_X' : @Right.Monoidal.Model (Modules X') _ _ _ _ _ _ _)
    (hE_qcoh : derivedQuasiCoherentModuleProperty X E) :
    IsIso (DerivedQCoh.tensorPushforwardBaseChangeMap g' f' f g sq T_X T_X'
      ⟨E, hE_qcoh⟩ G) := sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
