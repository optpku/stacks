module

public import ReasLib.Algebra.Homology.CochainComplex.Bounded
public import stacks_project.Chap75.Lemma_75_21_4_Comparison
public import stacks_project.Chap77.Theorem_77_4_7_FlatOver

/-!
# Tensor-pushforward base change for a relatively flat bounded-above complex

On a cartesian square of algebraic spaces whose vertical morphism is quasi-compact and
quasi-separated, formation of `Rf_*(E ⊗^L G)` commutes with arbitrary base change when
`G` is a bounded-above complex of quasi-coherent modules flat over the target.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory Limits
open CategoryTheory.DerivedCategory CategoryTheory.DerivedCategory.DerivedTensor
open CategoryTheory.MonoidalCategory ComplexShape

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

/-- Lemma 75.21.4: let `S` be a scheme and let `f : X ⟶ Y` be a quasi-compact and
quasi-separated morphism of algebraic spaces over `S`. Let `E` be in `D_QCoh(𝒪_X)`, and
let `G` be a bounded-above complex of quasi-coherent `𝒪_X`-modules flat over `Y`. Then
formation of `Rf_*(E ⊗^L G)` commutes with arbitrary base change: for every morphism
`g : Y' ⟶ Y` and every cartesian square, the comparison
`Lg^* Rf_*(E ⊗^L Q(G)) ⟶ Rf'_*(L(g')^* E ⊗^L Q((g')^* G))` is an isomorphism, using
ordinary termwise pullback of `G` on the right rather than derived pullback.
Relative flatness of each `G.X n` is the Comparison-side étale-chart condition
`Modules.flatOverAt`, because `Chap67.flatOver` is not importable beside Lemma 75.21.2. -/
@[stacks 0A1K]
theorem pushforwardTensorBaseChange_isIso
    {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}
    [MonoidalCategory (ModuleDerived X)] [MonoidalCategory (ModuleDerived X')]
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f]
    [(ModuleDerived.pullback g').Monoidal]
    [IsIso (ModuleDerived.pullbackCompComparison f' g)]
    [IsIso (ModuleDerived.pullbackCompComparison g' f)]
    (sq : IsPullback g' f' f g)
    (T_X : @Right.Monoidal.Model (Modules X) _ _ _ _ _ _ _)
    (T_X' : @Right.Monoidal.Model (Modules X') _ _ _ _ _ _ _)
    (E : DerivedQCoh X) (G : CochainComplex (Modules X) ℤ)
    (hG_minus : CochainComplex.minus (Modules X) G)
    (hG_qcoh : ∀ n : ℤ, (G.X n).IsQuasicoherent)
    (hG_flat : ∀ n : ℤ, ∀ x, Modules.flatOverAt (G.X n) f x) :
    IsIso (tensorPushforwardBaseChangeMap g' f' f g sq T_X T_X' E G) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
