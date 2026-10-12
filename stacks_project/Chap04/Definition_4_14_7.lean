/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Products
import StacksCheckRecall

@[expose] public section

namespace CategoryTheory.Limits

universe v u w

variable {C : Type u} [Category.{v} C]
variable {I : Type w} (M : I → C) [HasCoproduct M]

/- The source needs the coproduct object, not merely its existence. The verified candidates are
`HasCoproduct`, which only records existence, `sigmaObj`, whose body is exactly
`colimit (Discrete.functor M)`, and `Sigma.isoColimit`, which is a more general comparison for an
arbitrary discrete-domain functor and requires redundant colimit data here. Thus `sigmaObj` is the
exact family-level owner: its `HasCoproduct M` parameter recovers the source's "if it exists"
boundary, and the recall exposes both the `∐ M` notation and the general colimit API downstream. -/

/- Definition 4.14.7: for a family `M : I → C`, its coproduct `∐ M` is
`colimit (Discrete.functor M)` when that colimit exists. -/
@[stacks 002J "coproduct as the colimit of the discrete family diagram"]
#check (sigmaObj M : C)

end CategoryTheory.Limits
