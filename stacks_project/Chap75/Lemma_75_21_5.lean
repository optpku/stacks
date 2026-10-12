/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.Bounded
public import stacks_project.Chap75.Definition_75_14_1_PerfectApproximation
public import stacks_project.Chap75.Lemma_75_13_6_PseudoCoherent
public import stacks_project.Chap75.Lemma_75_21_5_Comparison
public import stacks_project.Chap77.Theorem_77_4_7_FlatOver

/-!
# Internal-Hom pushforward base change for a relatively flat complex

On a cartesian square of algebraic spaces whose vertical morphism is quasi-compact and
quasi-separated, formation of `Rf_* RHom(E, G)` commutes with arbitrary base change when
either `E` is perfect and `G` is bounded above, or `E` is pseudo-coherent and `G` is
bounded, with terms quasi-coherent and flat over the target.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory Limits
open CategoryTheory.DerivedCategory CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed ComplexShape

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

/-- Lemma 75.21.5 (1): let `S` be a scheme and let `f : X ⟶ Y` be a quasi-compact and
quasi-separated morphism of algebraic spaces over `S`. Let `E` be a perfect object of
`D(𝒪_X)`, and let `G` be a bounded-above complex of quasi-coherent `𝒪_X`-modules flat
over `Y`. Then formation of `Rf_* RHom(E, G)` commutes with arbitrary base change: for
every morphism `g : Y' ⟶ Y` and every cartesian square, the comparison
`Lg^* Rf_* RHom(E, Q(G)) ⟶ Rf'_* RHom(L(g')^* E, Q((g')^* G))` is an isomorphism, using
ordinary termwise pullback of `G` on the right rather than derived pullback.
Relative flatness of each `G.X n` is the Comparison-side étale-chart condition
`Modules.flatOverAt`, because `Chap67.flatOver` is not importable beside Lemma 75.21.2. -/
@[stacks 08JQ]
theorem pushforwardInternalHomBaseChange_isIso_of_isPerfect
    {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}
    [MonoidalCategory (ModuleDerived X)] [BraidedCategory (ModuleDerived X)]
    [MonoidalCategory (ModuleDerived X')] [BraidedCategory (ModuleDerived X')]
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f]
    [(ModuleDerived.pullback g').Monoidal]
    [IsIso (ModuleDerived.pullbackCompComparison f' g)]
    [IsIso (ModuleDerived.pullbackCompComparison g' f)]
    (sq : IsPullback g' f' f g) (H_X : MonoidalClosed (ModuleDerived X))
    (H_X' : MonoidalClosed (ModuleDerived X')) (E : ModuleDerived X)
    (G : CochainComplex (Modules X) ℤ) (hE : ModuleDerived.IsPerfect E)
    (hG_minus : CochainComplex.minus (Modules X) G)
    (hG_qcoh : ∀ n : ℤ, (G.X n).IsQuasicoherent)
    (hG_flat : ∀ n : ℤ, ∀ x, Modules.flatOverAt (G.X n) f x) :
    IsIso (internalHomPushforwardBaseChangeMap g' f' f g sq H_X H_X' E G) :=
  sorry

/-- Lemma 75.21.5 (2): let `S` be a scheme and let `f : X ⟶ Y` be a quasi-compact and
quasi-separated morphism of algebraic spaces over `S`. Let `E` be a pseudo-coherent
object of `D(𝒪_X)`, and let `G` be a bounded complex of quasi-coherent `𝒪_X`-modules
flat over `Y`. Then formation of `Rf_* RHom(E, G)` commutes with arbitrary base change:
for every morphism `g : Y' ⟶ Y` and every cartesian square, the comparison
`Lg^* Rf_* RHom(E, Q(G)) ⟶ Rf'_* RHom(L(g')^* E, Q((g')^* G))` is an isomorphism, using
ordinary termwise pullback of `G` on the right rather than derived pullback.
Relative flatness of each `G.X n` is the Comparison-side étale-chart condition
`Modules.flatOverAt`, because `Chap67.flatOver` is not importable beside Lemma 75.21.2. -/
@[stacks 08JQ]
theorem pushforwardInternalHomBaseChange_isIso_of_isPseudoCoherent
    {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}
    [MonoidalCategory (ModuleDerived X)] [BraidedCategory (ModuleDerived X)]
    [MonoidalCategory (ModuleDerived X')] [BraidedCategory (ModuleDerived X')]
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f]
    [(ModuleDerived.pullback g').Monoidal]
    [IsIso (ModuleDerived.pullbackCompComparison f' g)]
    [IsIso (ModuleDerived.pullbackCompComparison g' f)]
    (sq : IsPullback g' f' f g) (H_X : MonoidalClosed (ModuleDerived X))
    (H_X' : MonoidalClosed (ModuleDerived X')) (E : ModuleDerived X)
    (G : CochainComplex (Modules X) ℤ) (hE : IsPseudoCoherent X E)
    (hG_bounded : CochainComplex.bounded (Modules X) G)
    (hG_qcoh : ∀ n : ℤ, (G.X n).IsQuasicoherent)
    (hG_flat : ∀ n : ℤ, ∀ x, Modules.flatOverAt (G.X n) f x) :
    IsIso (internalHomPushforwardBaseChangeMap g' f' f g sq H_X H_X' E G) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
