/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Homology.DegreewiseSplit.CochainHomology
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {S : ShortComplex (CochainComplex C ℤ)}
variable (hS : S.ShortExact)
variable (σ : ∀ n : ℤ, (S.degreewise n).Splitting) (i : ℤ)

/- Lemma 12.14.11: the cohomology boundary of the degreewise-split triangle is the boundary in
the long exact cohomology sequence. -/
@[stacks 011K]
#check (CategoryTheory.ShortComplex.ShortExact.DegreewiseSplit.Cochain.boundary_eq_δ hS σ i :
  CochainComplex.homologyδOfTriangle
      (CochainComplex.triangleOfDegreewiseSplit S σ) i (i + 1) rfl =
    hS.δ i (i + 1) rfl)
