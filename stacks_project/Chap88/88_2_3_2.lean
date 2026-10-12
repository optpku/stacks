/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.CommAlgCat.TopologicallyFiniteType.BaseChange
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

variable {A1 A2 : Type u} [CommRing A1] [CommRing A2] [Algebra A1 A2]

/- 88.2.3.2: the completed base-change functor sends `B` to the `I2`-adic
completion of `B ⊗[A1] A2`. -/
@[stacks 0AK0] #check (CommAlgCat.TopologicallyFiniteType.baseChange :
  ∀ (I1 : Ideal A1) (I2 : Ideal A2) {c : ℕ}, 1 ≤ c →
    I1.map (algebraMap A1 A2) ^ c ≤ I2 → I2.FG →
      CommAlgCat.TopologicallyFiniteType.{u} A1 I1 ⥤
        CommAlgCat.TopologicallyFiniteType.{u} A2 I2)
