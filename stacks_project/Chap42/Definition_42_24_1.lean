module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.ChowGroup.FirstChern.Divisor

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

/- Definition 42.24.1: the Chow class of the divisor of any nonzero meromorphic section of
an invertible module is the first Chern class capped with the fundamental cycle. -/
@[stacks 02SJ] #check
  (AlgebraicGeometry.Scheme.Modules.firstChernClassCap_fundamental_eq_divisorClass :
    ∀ {S X : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType p]
        (δ : S → ℤ) [IsDimensionFunction δ] [IsIntegral X]
        (ℒ : X.Modules) [Scheme.Modules.Invertible ℒ]
        (s : X.toLocallyRingedSpace.meromorphicSections ℒ) (hs : s ≠ 0)
        (k : ℤ) (hdim : p.relativeDimensionFunction δ (genericPoint X) = k + 1),
      Scheme.Modules.firstChernClassCap p δ ℒ k
          (@CycleGroup.fundamental X (LocallyOfFiniteType.isLocallyNoetherian p)
            (p.relativeDimensionFunction δ) (k + 1)) =
        Scheme.Modules.MeromorphicSection.relativeDivisorClass p δ ℒ s hs k hdim)
