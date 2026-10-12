/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap92.Lemma_92_10_1_Maps
public import ReasLib.AlgebraicTopology.SimplicialObject.Homotopy
import Mathlib.Tactic.CrossRefAttribute

/-!
# Homotopy of Frobenius maps on the standard resolution

In characteristic `p`, the functoriality map of the standard resolution induced by the
Frobenius square is simplicially homotopic to degreewise Frobenius.
-/

@[expose] public section

open CategoryTheory
open CommRingCat.Under
open PolynomialResolution
open PolynomialResolution.Frobenius
open Under

universe u

namespace CategoryTheory.CommRingCat.Under
namespace PolynomialResolution
namespace Frobenius

/-- Lemma 92.10.1. Let `A ⟶ B` be a ring map with `p = 0` in `A`. Let `P_•` be the
standard resolution of `B` over `A`. The map `P_• ⟶ P_•` induced by the diagram of
Frobenius endomorphisms `F_A` and `F_B` discussed in Section 92.6 is homotopic to the
Frobenius endomorphism `P_• ⟶ P_•` given by Frobenius on each `P_n`. -/
@[stacks 0G5Y]
theorem functoriality_homotopic_degreewise
    (p : ℕ) [Fact p.Prime] {A : CommRingCat.{u}} (hp : (p : A) = 0) (B : Under A) :
    SimplicialObject.Homotopic (functoriality p hp B) (degreewise p hp B) :=
  sorry

end Frobenius
end PolynomialResolution
end CategoryTheory.CommRingCat.Under
