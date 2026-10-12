/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.FieldTheory.IntermediateField.GeneratorTower
public import Mathlib.FieldTheory.Minpoly.Field
import StacksCheckRecall

@[expose] public section

universe u v

section

variable (F : Type u) (K : Type v)
variable [Field F] [Field K] [Algebra F K]

namespace Situation_9_12_7

variable {K}
variable {n : ℕ}

open FieldExtension
open scoped IntermediateField

/- Situation 9.12.7 presents a finite extension through the textbook stages
`K_i = F(α₁, ..., αᵢ)`.  The stages themselves are owned by
`FieldExtension.adjoinStage`; this namespace retains only the source-facing notation
and the associated minimal-polynomial presentation. -/

/- Situation 9.12.7 (Tag 09H6): the textbook finite generator stages are the shared
`FieldExtension.adjoinStage` construction; no separate generated-extension package is
needed. -/
@[stacks 09H6]
#check FieldExtension.adjoinStage

-- Local declaration justification (source-local notation): this is the book's stage notation,
-- confined to the Situation 9.12.7 presentation namespace rather than a reusable global API.
/-- The source presentation `K[F, α; i] = F(α₁, ..., αᵢ)`. -/
scoped[Situation_9_12_7] notation "K[" F ", " α "; " i "]" =>
  FieldExtension.adjoinStage F α i

open scoped Situation_9_12_7

-- Local declaration justification (source-local notation): this is the book's polynomial `P_i`,
-- defined only to state the successive-root presentation built on the preceding stage notation.
/-- The minimal polynomial of `α i` over the preceding source stage. -/
scoped[Situation_9_12_7] notation "P[" F ", " α "; " i "]" =>
  minpoly (K[F, α; Fin.castSucc i]) (α i)

end Situation_9_12_7

end
