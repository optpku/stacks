/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.DescentDatum.FaithfullyFlat
import StacksCheckRecall

universe u

/- Theorem 59.16.7: If A ⟶ B is faithfully flat, then every module descent
datum relative to A ⟶ B is effective. -/
@[stacks 03OD] #check
  (@Module.DescentDatum.isEffective_of_faithfullyFlat :
    ∀ {A B N : Type u} [CommRing A] [CommRing B] [Algebra A B]
      [Module.FaithfullyFlat A B] [AddCommGroup N] [Module A N] [Module B N]
      [IsScalarTower A B N] [SMulCommClass A B N]
      (D : Module.DescentDatum A B N), D.IsEffective)
