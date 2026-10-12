/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.ChowGroup.FirstChern.ZeroScheme

open CategoryTheory

noncomputable section

universe u


namespace AlgebraicGeometry.Scheme.Modules

/- Lemma 42.24.2 (1): the divisor cycle of a nonzero global section of an invertible
module is the cycle of its zero scheme. -/
@[stacks 02SK]
#check (AlgebraicGeometry.Scheme.Modules.divisorCycle_eq_zeroCycle :
  ∀ {S X : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType p]
    (δ : S → ℤ) [IsDimensionFunction δ] [IsIntegral X]
    (ℒ : X.Modules) [Invertible ℒ] (s : ℒ.sections) (hs : s ≠ 0)
    (k : ℤ) (hdim : p.relativeDimensionFunction δ (genericPoint X) = k + 1),
    relativeNonzeroSectionDivisorCycle p δ ℒ s hs k hdim =
      relativeZeroCycleGroup p δ ℒ s k)

/- Lemma 42.24.2 (2): the first Chern class of an invertible module capped with the
fundamental cycle is the Chow class of the zero scheme of a nonzero global section. -/
@[stacks 02SK]
#check (AlgebraicGeometry.Scheme.Modules.firstChernClassCap_fundamental_eq_zeroCycleClass :
  ∀ {S X : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType p]
    (δ : S → ℤ) [IsDimensionFunction δ] [IsIntegral X]
    (ℒ : X.Modules) [Invertible ℒ] (s : ℒ.sections) (_ : s ≠ 0)
    (k : ℤ) (_ : p.relativeDimensionFunction δ (genericPoint X) = k + 1),
    firstChernClassCap p δ ℒ k
        (@CycleGroup.fundamental X (LocallyOfFiniteType.isLocallyNoetherian p)
          (p.relativeDimensionFunction δ) (k + 1)) =
      @chowClass X (LocallyOfFiniteType.isLocallyNoetherian p)
        (p.relativeDimensionFunction δ) inferInstance k
        (relativeZeroCycleGroup p δ ℒ s k))

end AlgebraicGeometry.Scheme.Modules
