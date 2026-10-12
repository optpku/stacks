/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.HomologySequenceLemmas
import StacksCheckRecall

@[expose] public section

open ComplexShape HomologicalComplex.HomologySequence

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {S : ShortComplex (CochainComplex C ℤ)} (hS : S.ShortExact) (n : ℤ)

/- Equation 22.4.2.1 (09JK): the first four objects and three arrows of the canonical exact
cohomology sequence are
`H^n(S.X₁) ⟶ H^n(S.X₂) ⟶ H^n(S.X₃) ⟶ H^(n + 1)(S.X₁)`.
They are the twofold right truncation of `composableArrows₅`. -/
@[stacks 09JK] #check
  ((composableArrows₅ hS n (n + 1) (up_mk n (n + 1) rfl)).δlast.δlast :
    ComposableArrows C 3)

/- The third displayed arrow is the canonical connecting morphism. -/
#check (hS.δ n (n + 1) (up_mk n (n + 1) rfl) :
  S.X₃.homology n ⟶ S.X₁.homology (n + 1))

/- Exactness at the two middle objects of the displayed four-term window. -/
#check hS.homology_exact₂ n
#check hS.homology_exact₃ n (n + 1) (up_mk n (n + 1) rfl)

/- The canonical six-object extension of the displayed window is exact throughout. -/
#check (composableArrows₅_exact hS n (n + 1) (up_mk n (n + 1) rfl) :
  (composableArrows₅ hS n (n + 1) (up_mk n (n + 1) rfl)).Exact)

end CategoryTheory
