/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.OreLocalization.Ring
public import ReasLib.CategoryTheory.MorphismProperty.Localization.OreLocalization
public import ReasLib.CategoryTheory.Preadditive.SingleObj
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.MorphismProperty
open OreLocalization

universe u

variable {R : Type u}

namespace CategoryTheory.SingleObj

variable [Ring R]

/- Remark 4.27.3 (1): a ring is canonically a one-object preadditive category. -/
@[stacks 0BM1 "rings as one-object preadditive categories"]
#check (inferInstance : Preadditive (SingleObj R))

variable (S : Submonoid R)

/- Remark 4.27.3 (2): the submonoid `S` satisfies MS1 on the one-object category. -/
@[stacks 0BM1 "multiplicative subsets as multiplicative morphism properties"]
#check (submonoidProperty.isMultiplicative S : (submonoidProperty S).IsMultiplicative)

/- Remark 4.27.3 (3): right calculus of fractions on `SingleObj R` is equivalent to right
permutability and right reversibility of `S`. -/
@[stacks 0BM1 "right calculus of fractions and right denominator conditions"]
#check (Calculus.right_iff_denominator S :
  (submonoidProperty S).HasRightCalculusOfFractions ↔
    (∀ (r : R) (s : S), ∃ (r' : R) (s' : S), r * s' = s * r') ∧
      ∀ (r₁ r₂ : R) (s : S), s * r₁ = s * r₂ →
        ∃ s' : S, r₁ * s' = r₂ * s')

/- Remark 4.27.3 (4): left calculus of fractions on `SingleObj R` is equivalent to left
reversibility and left permutability of `S`. -/
@[stacks 0BM1 "left calculus of fractions and left denominator conditions"]
#check (Calculus.left_iff_denominator S :
  (submonoidProperty S).HasLeftCalculusOfFractions ↔
    (∀ (r₁ r₂ : R) (s : S), r₁ * s = r₂ * s →
        ∃ s' : S, s' * r₁ = s' * r₂) ∧
      ∀ (r : R) (s : S), ∃ (r' : R) (s' : S), s' * r = r' * s)

variable [OreSet S]

/- Remark 4.27.3 (5): the functor induced by the Ore-localization ring homomorphism is additive. -/
@[stacks 0BM1 "additivity of the Ore-localization functor"]
#check
  ((numeratorRingHom (R := R) (S := S)).toAdditiveFunctor :
    SingleObj R ⥤+ SingleObj R[S⁻¹])

/- Remark 4.27.3 (6): the Ore-localization functor is the categorical localization at `S`. -/
@[stacks 0BM1 "Ore ring localization as categorical localization"]
#check
  (inferInstance :
    ((numeratorRingHom (R := R) (S := S)).toMonoidHom.toFunctor :
      SingleObj R ⥤ SingleObj R[S⁻¹]).IsLocalization
        (submonoidProperty S))

end CategoryTheory.SingleObj
