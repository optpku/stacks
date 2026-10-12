/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap82.Definition_82_15_1_RationalEquivalence
public import stacks_project.Chap82.Lemma_82_20_1_Key_formula_Term

/-!
# The key formula for meromorphic-section divisors on algebraic spaces

In Situation 82.2.1 the locally finite sum of the order-weighted restricted
divisors equals the boundary of the corresponding tame symbols, as cycles.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory
open Function Set Topology
open AlgebraicGeometry.AlgebraicSpace.Hom
open AlgebraicGeometry.AlgebraicSpace.PrimeDivisor

noncomputable section

universe u v

namespace AlgebraicGeometry.AlgebraicSpace.Hom

/-- Lemma 82.20.1 (Key formula): In Situation 82.2.1, for good integral `X / B`
of `δ`-dimension `n` with invertible modules `L`, `N` and regular meromorphic
sections `s`, `t`, and a locally finite family of prime divisors `Z i`
containing every prime where `s` or `t` fails to generate the henselian fibre,
and the source's chosen local presentations `sData i`, `tData i`,
the `(n-2)`-cycle obtained by pushing forward
`ord_{B i}(f_i) div_{N|_{Z i}}(t_i|_{Z i}) - ord_{B i}(g_i) div_{L|_{Z i}}(s_i|_{Z i})`
equals the boundary of the tame symbols `∂_{B i}(f_i, g_i)`, as cycles. -/
@[stacks 0EQV]
theorem keyFormula {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f] [IsIntegral X]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (n : ℤ) (hX : deltaDimension f δ (univIrreducibleClosed X) = n)
    (L N : X.Modules) [isInvertibleObject L] [isInvertibleObject N]
    (s : meromorphicSections X L) (hs : IsRegularMeromorphicSection X L s)
    (t : meromorphicSections X N) (ht : IsRegularMeromorphicSection X N t)
    {I : Type v} (Z : I → PrimeDivisor X) (hZ : Injective Z)
    (hlocal : LocallyFinite fun i ↦ ((Z i).pointsSet : Set (Points X)))
    (hsAway : ∀ W : PrimeDivisor X, (∀ i, Z i ≠ W) → GeneratesHenselianFibre s W)
    (htAway : ∀ W : PrimeDivisor X, (∀ i, Z i ≠ W) → GeneratesHenselianFibre t W)
    (sData : ∀ i, KeyFormulaPresentation.LocalPresentation s (Z i))
    (tData : ∀ i, KeyFormulaPresentation.LocalPresentation t (Z i)) :
    AlgebraicCycle.locallyFiniteSum
        (fun i ↦ keyFormulaTerm f δ n hX L N (Z i) s hs t ht (sData i) (tData i))
        (keyFormulaTermsLocallyFinite f δ n hX L N Z s hs t ht hlocal sData tData) =
      (RationalEquivalence.boundary f δ (n - 2) (fun i ↦ (Z i).subspace)
          (fun i ↦ PrimeDivisor.instIsIntegral_space (Z i))
          (fun i ↦ primeDivisor_deltaDimension f δ n hX (Z i))
          (fun i ↦ tameSymbolOnSpace_ofGood f (Z i)
            (sData i).fraction
            (tData i).fraction) hlocal :
        Function.locallyFinsupp (Points X) ℤ) :=
  sorry

/-- The left-hand side of the key formula is an `(n-2)`-cycle. -/
theorem keyFormula_mem_cycleGroup {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f] [IsIntegral X]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (n : ℤ) (hX : deltaDimension f δ (univIrreducibleClosed X) = n)
    (L N : X.Modules) [isInvertibleObject L] [isInvertibleObject N]
    (s : meromorphicSections X L) (hs : IsRegularMeromorphicSection X L s)
    (t : meromorphicSections X N) (ht : IsRegularMeromorphicSection X N t)
    {I : Type v} (Z : I → PrimeDivisor X) (hZ : Injective Z)
    (hlocal : LocallyFinite fun i ↦ ((Z i).pointsSet : Set (Points X)))
    (hsAway : ∀ W : PrimeDivisor X, (∀ i, Z i ≠ W) → GeneratesHenselianFibre s W)
    (htAway : ∀ W : PrimeDivisor X, (∀ i, Z i ≠ W) → GeneratesHenselianFibre t W)
    (sData : ∀ i, KeyFormulaPresentation.LocalPresentation s (Z i))
    (tData : ∀ i, KeyFormulaPresentation.LocalPresentation t (Z i)) :
    AlgebraicCycle.locallyFiniteSum
        (fun i ↦ keyFormulaTerm f δ n hX L N (Z i) s hs t ht (sData i) (tData i))
        (keyFormulaTermsLocallyFinite f δ n hX L N Z s hs t ht hlocal sData tData) ∈
      cycleGroup f δ (n - 2) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom
