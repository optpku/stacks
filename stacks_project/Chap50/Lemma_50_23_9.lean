/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.DeRham.Gysin.HodgeCup

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory ComplexShape
open DerivedCategory.DerivedTensor.Right.Monoidal Functor.RightDerived.Homotopy
open Scheme.Hom
open scoped DerivedTensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry
namespace Scheme
namespace DeRham
namespace Gysin

variable {Z X S : Scheme.{u}}

/- Lemma 50.23.9: if X → S is smooth and i : Z → X is a Koszul-regular closed immersion of
conormal rank c as in Lemma 50.23.3, then for α in H^q(X, Ω^p_{X/S}) one has
γ^{p,q}(α|_Z) = α ∪ γ^{0,0}(1) in H^{q+c}(X, Ω^{p+c}_{X/S}). -/
@[stacks 0G8C]
#check (AlgebraicGeometry.Scheme.DeRham.Gysin.hodgeCohomologyMap_restriction :
    ∀ {Z X S : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] [Scheme.Hom.FinitePresentation i]
      (f : X ⟶ S) [Smooth f] [IsKoszulRegularImmersion i] (c p q : ℕ)
      [SheafOfModules.IsFiniteLocallyFreeOfRank c (Scheme.Hom.conormalSheaf i)]
      [derivedMonoidal : MonoidalCategory (coefficientDerived f)]
      [qhMonoidal : AlgebraicGeometry.Scheme.DeRham.CoefficientQhMonoidal f]
      [globalLaxMonoidal : (globalDerivedFunctor f).LaxMonoidal]
      (T : CoefficientTensorModel f)
      (α : hodgeCohomologyObject f p (q : ℤ)),
    hodgeGysinAfterRestriction i f c p q α =
      Scheme.DeRham.hodgeCup f T α (hodgeFundamentalClassOne i f c))

end Gysin
end DeRham
end Scheme
end AlgebraicGeometry

end
