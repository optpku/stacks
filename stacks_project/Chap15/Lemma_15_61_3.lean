/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Tor.BaseChange
import StacksCheckRecall

/-!
# Flat Base Change for `Tor`

@stack 08HW

The reusable owner equips `Tor_n^R(A, B)` with its canonical
`A ⊗[R] B`-module structure and constructs the comparison along
`A ⊗[R] B → A' ⊗[R'] B'`.  This is the scalar extension appearing in
the source formula, rather than scalar extension along `R → R'` alone.
-/

@[expose] public section

/- Lemma 15.61.3 (08HW): if `R'` is flat over `R`, `A'` is flat over
`A ⊗[R] R'`, and `B'` is flat over `R' ⊗[R] B`, then the canonical map
`Tor_n^R(A, B) ⊗[A ⊗[R] B] (A' ⊗[R'] B') ⟶ Tor_n^{R'}(A', B')`
is an isomorphism for every `n : ℕ`. -/
@[stacks 08HW "flat base change for Tor"]
#check @CategoryTheory.ModuleCat.Tor.Flat.BaseChange.comparison_isIso

#check @CategoryTheory.ModuleCat.Tor.TensorAction.obj
#check @CategoryTheory.ModuleCat.Tor.Flat.BaseChange.productMap
#check @CategoryTheory.ModuleCat.Tor.Flat.BaseChange.comparison
