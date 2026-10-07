module

public import ReasLib.Algebra.Module.DirectSumDevissage.SuccessiveQuotient
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Kaplansky devissages and countable direct sums

This leaf owns the equivalence between an internal direct sum of countably generated modules and
an ordinal-indexed direct-sum devissage with countably generated successor quotients.
-/

universe u v w

namespace Module

variable {R : Type u} [Ring R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- An internal direct sum of countably generated modules admits a Kaplansky direct-sum devissage. -/
@[stacks 058W "Kaplansky devissage from a countable direct sum"]
theorem exists_kaplanskyDevissage_of_isDirectSumOfCountablyGenerated
    (hM : IsDirectSumOfCountablyGenerated.{u, v, w} R M) :
    ∃ D : DirectSumDevissage.{u, v, w} R M, D.IsKaplansky := sorry

/-- A Kaplansky direct-sum devissage exhibits the ambient module as an internal direct sum of
countably generated modules. -/
@[stacks 058W "countable direct sum from a Kaplansky devissage"]
theorem isDirectSumOfCountablyGenerated_of_kaplanskyDevissage
    (D : DirectSumDevissage.{u, v, w} R M) (hD : D.IsKaplansky) :
    IsDirectSumOfCountablyGenerated.{u, v, w} R M := sorry

/-- Lemma 10.84.3 (Tag 058W): an `R`-module is an internal direct sum of countably generated
modules exactly when it admits a Kaplansky direct-sum devissage. -/
@[stacks 058W "countable direct sums and Kaplansky devissages"]
theorem isDirectSumOfCountablyGenerated_iff_hasKaplanskyDevissage :
    IsDirectSumOfCountablyGenerated.{u, v, w} R M ↔
      ∃ D : DirectSumDevissage.{u, v, w} R M, D.IsKaplansky := sorry

end Module
