/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Flatness.MittagLeffler.TensorProduct
import StacksCheckRecall

/-!
# Tensor products and Mittag-Leffler modules

@stack 059M
-/

@[expose] public section

/- Proposition 10.89.5: an `R`-module `M` is Mittag-Leffler if and only if, for every family
`Q`, the canonical map `M ⊗[R] (∀ a, Q a) → ∀ a, M ⊗[R] Q a` is injective. -/
@[stacks 059M]
#check @Module.MittagLeffler.iff_piRightHom_injective
