/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale.RegularExtension
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme.FiniteEtale

/- Lemma 58.31.2: a finite étale cover over a dense open extends across regular complementary
stalks when it is unramified in codimension one. -/
@[stacks 0H2W]
#check
  (AlgebraicGeometry.Scheme.FiniteEtale.exists_extension_of_unramifiedInCodimensionOne :
    ∀ {X : Scheme.{u}} [IsLocallyNoetherian X] (U : X.Opens) (hU : Dense (U : Set X))
      [Fact (∀ x : X, x ∉ (U : Set X) → IsRegularLocalRing (X.presheaf.stalk x))]
      (Y : Scheme.FiniteEtale U.toScheme)
      (hY : IsUnramifiedInCodimensionOne U hU Y),
      ∃ Y' : Scheme.FiniteEtale X,
        Nonempty ((finiteEtaleBaseChange U.ι).obj Y' ≅ Y))

end AlgebraicGeometry.Scheme.FiniteEtale
