module

public import stacks_project.Chap71.Definition_71_7_1_AssociatedSheaf
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

/- Definition 71.7.1 (1): the invertible sheaf 𝒪_X(D) associated to an effective Cartier
divisor D ⊂ X is Hom_{𝒪_X}(I_D, 𝒪_X) = I_D^{⊗ -1}. -/
@[stacks 0841] #check
  (Hom.associatedSheaf :
    {S : Scheme.{u}} → {D X : AlgebraicSpace S} →
      (i : D ⟶ X) → [IsEffectiveCartierDivisor i] → X.Modules)

/- Definition 71.7.1 (2): the canonical section 1_D of 𝒪_X(D) corresponds to the inclusion
I_D ⟶ 𝒪_X. -/
@[stacks 0841] #check
  (Hom.canonicalSection :
    {S : Scheme.{u}} → {D X : AlgebraicSpace S} →
      (i : D ⟶ X) → [IsEffectiveCartierDivisor i] →
      (Hom.associatedSheaf i).sections)

/- Definition 71.7.1 (3): the negative sheaf 𝒪_X(-D) is 𝒪_X(D)^{⊗ -1} = I_D. -/
@[stacks 0841] #check
  (Hom.negSheaf :
    {S : Scheme.{u}} → {D X : AlgebraicSpace S} →
      (i : D ⟶ X) → [IsEffectiveCartierDivisor i] → X.Modules)

/- Definition 71.7.1 (4): for effective Cartier divisors D and D', the difference sheaf
𝒪_X(D - D') is 𝒪_X(D) ⊗ 𝒪_X(-D'). -/
@[stacks 0841] #check
  (Hom.differenceSheaf :
    {S : Scheme.{u}} → {D D' X : AlgebraicSpace S} →
      (i : D ⟶ X) → (i' : D' ⟶ X) →
      [IsEffectiveCartierDivisor i] → [IsEffectiveCartierDivisor i'] → X.Modules)
