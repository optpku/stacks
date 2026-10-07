module

public import ReasLib.Algebra.Homology.CochainComplex.Bounded
public import stacks_project.Chap67.Lemma_67_28_8_FinitePresentation
public import stacks_project.Chap67.Lemma_67_31_6_ModuleSupport
public import stacks_project.Chap75.Definition_75_5_1_DerivedQCoh
public import stacks_project.Chap75.Definition_75_14_1_PerfectApproximation
public import stacks_project.Chap75.Lemma_75_3_1_Pushforward
public import stacks_project.Chap75.Lemma_75_7_3_ProperOver
public import stacks_project.Chap75.Lemma_75_21_5_Comparison
public import stacks_project.Chap77.Theorem_77_4_7_FlatOver

/-!
# Perfect derived pushforward of internal Hom into a bounded relatively flat finitely presented complex

Along a morphism of finite presentation of algebraic spaces, the derived pushforward of the
derived internal Hom from a perfect object into a bounded complex of finitely presented modules
that are flat over the target with support proper over the target is perfect, and its formation
commutes with arbitrary base change.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory Limits
open CategoryTheory.DerivedCategory CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- Lemma 75.25.8 (1): let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of finite
presentation between algebraic spaces over `S`. Let `E` be a perfect object of `D(𝒪_X)`,
and let `G` be a bounded complex of finitely presented `𝒪_X`-modules, flat over `Y`,
with support proper over `Y`. Then
`K = (Modules.pushforwardDerived f).obj ((ihomOf H E).obj (DerivedCategory.Q.obj G))`
is a perfect object of `D(𝒪_Y)`. -/
@[stacks 0A1R]
theorem pushforwardDerived_internalHom_isPerfect_of_finitePresentation
    [MonoidalCategory (ModuleDerived X)]
    (f : X ⟶ Y) [FinitePresentation f] (H : MonoidalClosed (ModuleDerived X))
    (E : ModuleDerived X) (hE : IsPerfect E)
    (G : CochainComplex (Modules X) ℤ)
    (hG_bounded : CochainComplex.bounded (Modules X) G)
    (hG_fp : ∀ i : ℤ, (G.X i).IsFinitePresentation)
    (hG_flat : ∀ i : ℤ, ∀ x, Modules.flatOverAt (G.X i) f x)
    (hG_support : ∀ i : ℤ, ClosedSubset.IsProperOver f
      (Closeds.closure (Modules.moduleSupport (G.X i)))) :
    IsPerfect ((Modules.pushforwardDerived f).obj
      ((ihomOf H E).obj (DerivedCategory.Q.obj G))) := sorry

/-- Lemma 75.25.8 (2): under the same hypotheses, formation of
`K = Rf_* RHom(E, Q(G))` commutes with arbitrary base change: for every cartesian square,
the comparison `Lg^* Rf_* RHom(E, Q(G)) ⟶ Rf'_* RHom(L(g')^* E, Q((g')^* G))` is an
isomorphism, using ordinary termwise pullback of `G` on the right. -/
@[stacks 0A1R]
theorem pushforwardDerived_internalHom_baseChange_isIso_of_finitePresentation
    (f : X ⟶ Y) [FinitePresentation f] (E : ModuleDerived X) (hE : IsPerfect E)
    (G : CochainComplex (Modules X) ℤ)
    (hG_bounded : CochainComplex.bounded (Modules X) G)
    (hG_fp : ∀ i : ℤ, (G.X i).IsFinitePresentation)
    (hG_flat : ∀ i : ℤ, ∀ x, Modules.flatOverAt (G.X i) f x)
    (hG_support : ∀ i : ℤ, ClosedSubset.IsProperOver f
      (Closeds.closure (Modules.moduleSupport (G.X i))))
    {X' Y' : AlgebraicSpace S}
    [MonoidalCategory (ModuleDerived X)] [BraidedCategory (ModuleDerived X)]
    [MonoidalCategory (ModuleDerived X')] [BraidedCategory (ModuleDerived X')]
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y)
    [(ModuleDerived.pullback g').Monoidal]
    [IsIso (ModuleDerived.pullbackCompComparison f' g)]
    [IsIso (ModuleDerived.pullbackCompComparison g' f)]
    (sq : IsPullback g' f' f g) (H_X : MonoidalClosed (ModuleDerived X))
    (H_X' : MonoidalClosed (ModuleDerived X')) :
    IsIso (DerivedQCoh.internalHomPushforwardBaseChangeMap g' f' f g sq H_X H_X' E G) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
