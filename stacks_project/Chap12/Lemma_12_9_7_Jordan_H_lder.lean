/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Abelian.JordanHolder
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {A : C}

/- Lemma 12.9.7 (Jordan-Hölder): the factors of two composition series from `0` to `A` agree up
to permutation and isomorphism. -/
@[stacks 0FCK]
#check @CompositionSeries.jordanHolderFactors C _ _ A

/- Equal-endpoint series are supported directly, without forcing the endpoints to be `⊥` and `⊤`. -/
#check @CompositionSeries.jordanHolderFactorsOfEndpoints C _ _ A
