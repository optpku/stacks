/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.FieldTheory.PurelyInseparable.Tower
import StacksCheckRecall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling for Lemma 9.14.9:
- primary domain: separable and inseparable degrees in towers of field extensions;
- sampled owner declarations:
  `Field.sepDegree`,
  `Field.insepDegree`,
  `Field.sepDegree_mul_sepDegree_of_isAlgebraic`,
  `Field.insepDegree_mul_insepDegree_of_isAlgebraic`;
- best owner abstraction: the canonical mathlib tower-law owners
  `Field.sepDegree_mul_sepDegree_of_isAlgebraic` and
  `Field.insepDegree_mul_insepDegree_of_isAlgebraic`;
- primitive data: only a tower `F ⟶ E ⟶ K` and the algebraicity of the middle extension `E / F`;
- derived API: the textbook display order `[K : F]ₛ = [K : E]ₛ [E : F]ₛ` and
  `[K : F]ᵢ = [K : E]ᵢ [E : F]ᵢ`, obtained from the canonical owners by symmetry and
  commutativity of cardinal multiplication.

Source/core/bridge triage:
- `source-facing`: the textbook multiplicativity formulas written in degree notation;
- `core/canonical`: the mathlib tower laws
  `Field.sepDegree_mul_sepDegree_of_isAlgebraic` and
  `Field.insepDegree_mul_insepDegree_of_isAlgebraic`;
- `bridge/view`: only the harmless reordering of factors into the textbook display order.

This file should therefore be pure canonical check. Keeping local wrapper theorems here would
duplicate the owner declarations without adding new mathematics.
-/

/- Lemma 9.14.9 (Multiplicativity) (1): the canonical owner for separable-degree multiplicativity
in a tower `K / E / F` is `Field.sepDegree_mul_sepDegree_of_isAlgebraic`. Through the notation
from Definition 9.14.7, its statement `[E : F]ₛ * [K : E]ₛ = [K : F]ₛ` is exactly the
textbook formula up to symmetry and commutativity. -/
@[stacks 09HK]
#check Field.sepDegree_mul_sepDegree_of_isAlgebraic

/- Lemma 9.14.9 (Multiplicativity) (2): the canonical owner for inseparable-degree multiplicativity
in a tower `K / E / F` is `Field.insepDegree_mul_insepDegree_of_isAlgebraic`. Through the notation
from Definition 9.14.7, its statement `[E : F]ᵢ * [K : E]ᵢ = [K : F]ᵢ` is exactly the
textbook formula up to symmetry and commutativity. -/
#check Field.insepDegree_mul_insepDegree_of_isAlgebraic
