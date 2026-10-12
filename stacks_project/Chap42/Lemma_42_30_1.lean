/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.ChowGroup.Gysin.FirstChern

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/- Lemma 42.30.1: for `k = n - 2`, Gysin pullback of the divisor of a nonzero
meromorphic section of `𝒩` equals `c₁(𝒩|Z(s)) ∩ [Z(s)]_(k + 1)` in the
degree-`k` Chow group of the effective Cartier divisor `Z(s)`. -/
@[stacks 02TM] #check
  (AlgebraicGeometry.Scheme.Modules.gysin_relativeDivisorCycle_eq_firstChern_fundamental :
    ∀ {S X : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType p]
      (δ : S → ℤ) [IsDimensionFunction δ] [IsIntegral X]
      (ℒ : X.Modules) [Invertible ℒ] (s : ℒ.sections)
      [IsEffectiveCartierDivisor (zeroSchemeι ℒ s)]
      (𝒩 : X.Modules) [Invertible 𝒩]
      (t : X.toLocallyRingedSpace.meromorphicSections 𝒩) (ht : t ≠ 0)
      (k : ℤ)
      (hX : p.relativeDimensionFunction δ (genericPoint X) = (k + 1) + 1),
      gysin p δ ℒ s k
          (MeromorphicSection.relativeDivisorCycle p δ 𝒩 t ht (k + 1) hX) =
        firstChernClassCap (zeroSchemeι ℒ s ≫ p) δ
          ((pullback (zeroSchemeι ℒ s)).obj 𝒩) k
          (@CycleGroup.fundamental (zeroScheme ℒ s)
            (@zeroSchemeIsLocallyNoetherian X
              (LocallyOfFiniteType.isLocallyNoetherian p) ℒ inferInstance s)
            ((zeroSchemeι ℒ s ≫ p).relativeDimensionFunction δ) (k + 1)))

end AlgebraicGeometry.Scheme.Modules
