/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap93.Lemma_93_12_1_Lift
import StacksCheckRecall

/-!
# Flat lifts versus bounded-above derived lifts
-/

@[expose] public section

open CategoryTheory.ModuleCat

/- Lemma 93.12.1: for a surjection `A' → A` of commutative rings with nilpotent kernel, a
flat map `A' → P'`, `P := P' ⊗[A'] A`, and an `A`-flat `P`-module `M`, existence of an
`A'`-flat `P'`-module `M'` with `M' ⊗[P'] P ≅ M` is equivalent to existence of
`K' ∈ D⁻(ModuleCat P')` with `K' ⊗[P']^L P ≅ single0 M`. -/
@[stacks 0DZ1]
#check @NilpotentLift.existsFlatLift_iff_existsBoundedAboveDerivedLift

end
