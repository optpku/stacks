/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap82.Definition_82_17_1_Cycle
public import stacks_project.Chap82.Definition_82_17_1_Chow
public import stacks_project.Chap82.Lemma_82_6_3_AssociatedCycle
public import stacks_project.Chap71.Definition_71_7_6_ZeroScheme
public import stacks_project.Chap82.Lemma_82_17_2_MeromorphicSection

/-!
# Divisor and first Chern class of a nonzero section

The divisor cycle and its Chow class use the canonical operators of Definition
82.17.1. The zero scheme retains its scheme-theoretic multiplicities through
the existing associated-cycle construction.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom

variable {S : Scheme.{u}} {B X : AlgebraicSpace S}
  [UniversallyCatenary B] [IsQuasiSeparated B]
variable (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
variable (δ : Points B → ℤ) [IsDimensionFunction δ]
variable [IsIntegral X]

/-- The zero-scheme cycle of a nonzero section has degree `dim_δ(X) - 1`. -/
theorem zeroSchemeCycle_mem {L : X.Modules} [isInvertibleObject L]
    (s : L.sections) (hs : s ≠ 0) :
    @ClosedSubspace.cycle S X (LocallyOfFiniteType.isLocallyNoetherian f)
        (zeroScheme L s) (relativeDimensionFunction f δ)
        (deltaDimension f δ (univIrreducibleClosed X) - 1) ∈
      codimOneCycleGroup f δ := sorry

/-- Lemma 82.17.2 (1): In Situation 82.2.1 let `X / B` be good and integral,
with `n = dim_δ(X)`. For an invertible module `L` and nonzero global section
`s`, its divisor is `[Z(s)]_{n-1}` in `Z_{n-1}(X)`. -/
@[stacks 0EQF]
theorem meromorphicSectionDivisorCycle_eq_zeroSchemeCycle
    {L : X.Modules} [isInvertibleObject L] (s : L.sections) (hs : s ≠ 0) :
    meromorphicSectionDivisorCycle f δ (toMeromorphicSection s)
        (@toMeromorphicSection_isRegular S X
          (LocallyOfFiniteType.isLocallyNoetherian f) inferInstance L inferInstance s hs) =
      @ClosedSubspace.cycle S X (LocallyOfFiniteType.isLocallyNoetherian f)
        (zeroScheme L s) (relativeDimensionFunction f δ)
        (deltaDimension f δ (univIrreducibleClosed X) - 1) := sorry

/-- Lemma 82.17.2 (2): In Situation 82.2.1 let `X / B` be good and integral,
with `n = dim_δ(X)`. For an invertible module `L` and nonzero global section
`s`, `c1(L) ∩ [X]` is `[Z(s)]_{n-1}` in `CH_{n-1}(X)`. -/
@[stacks 0EQF]
theorem firstChernCapFundamental_eq_zeroSchemeCycle
    {L : X.Modules} [isInvertibleObject L] (s : L.sections) (hs : s ≠ 0) :
    firstChernCapFundamental f δ L =
      chowClass f δ
        (@ClosedSubspace.cycle S X (LocallyOfFiniteType.isLocallyNoetherian f)
          (zeroScheme L s) (relativeDimensionFunction f δ)
          (deltaDimension f δ (univIrreducibleClosed X) - 1)) := sorry

end AlgebraicGeometry.AlgebraicSpace.Hom
