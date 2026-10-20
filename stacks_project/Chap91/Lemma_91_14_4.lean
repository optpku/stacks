module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening.Solution.Pushout

open CategoryTheory
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Hom

universe u

/- Lemma 91.14.4: if X is quasi-compact and quasi-separated and
DQ_X(ℱ) ⟶ DQ_X(𝒢) is an isomorphism, then the pushout functor FT along
φ : ℱ ⟶ 𝒢 of solutions of 91.13.0.1 for a first-order thickening i : B ⟶ B'
and a coefficient c : f⁻¹J ⟶ ℱ is an equivalence of categories. Coefficients
need not be quasi-coherent. Here DQ_X is the right adjoint of DerivedQCoh.inclusion
from Derived Categories of Spaces 75.19. -/
@[stacks 0D3Q] #check
  (AlgebraicGeometry.AlgebraicSpace.Hom.ThickeningSolution.pushout_isEquivalence :
    ∀ {S : Scheme.{u}} {X B B' : AlgebraicSpace S}
      (i : B ⟶ B') [IsFirstOrderThickening i] (f : X ⟶ B)
      [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
      {ℱ 𝒢 : X.Modules} (φ : ℱ ⟶ 𝒢) (c : ThickeningSolution.Coeff i f ℱ)
      [IsIso (SquareZeroAlgebraExtension.dqMap φ)],
      Functor.IsEquivalence (ThickeningSolution.pushoutFunctor i f φ c))
