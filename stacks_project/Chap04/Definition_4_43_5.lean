/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import StacksCheckRecall

@[expose] public section

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable (X Y : C)

/- `ExactPairing X Y` is the fixed-pair owner needed here: it stores a coevaluation
`𝟙_ C ⟶ X ⊗ Y`, an evaluation `Y ⊗ X ⟶ 𝟙_ C`, and exactly the two triangle identities.
The plausible alternatives `HasRightDual X` and `HasLeftDual Y` additionally choose a dual object,
so they are existence interfaces rather than owners for the source's specified `X` and `Y`. This
recall introduces no generalization: the Stacks left-dual datum and its corresponding right-dual
wording are both recovered from the same ordered pairing, while downstream results can reuse
mathlib's evaluation, coevaluation, Hom-equivalence, and adjunction API directly. -/

/- Definition 4.43.5: the textbook datum of a left dual `Y` of `X` is exactly the canonical
mathlib owner `ExactPairing X Y`; the same ordered pairing says that `X` is a right dual of `Y`. -/
@[stacks 0FFP "left dual data and the corresponding right dual relation"]
#check (ExactPairing X Y : Type v)

end CategoryTheory
