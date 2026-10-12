/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pushforward.Coproduct
public import stacks_project.Chap36.Lemma_36_4_1
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

variable {X S : Scheme.{u}} (f : X ⟶ S)
variable [AlgebraicGeometry.QuasiCompact f] [AlgebraicGeometry.QuasiSeparated f]
variable (I : Type u)

/- Lemma 36.4.5: for a quasi-compact and quasi-separated morphism `f`, the restricted
derived pushforward `DerivedQCoh.pushforward f` preserves arbitrary direct sums. -/
@[stacks 08DZ] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.pushforwardCohomologyIn.preservesCoproducts f I :
    PreservesColimitsOfShape (Discrete I) (DerivedQCoh.pushforward f))

end AlgebraicGeometry.Scheme.DerivedQCoh
