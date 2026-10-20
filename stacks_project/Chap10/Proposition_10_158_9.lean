/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.FieldTheory.Separable.Generated.CharZero
public import ReasLib.RingTheory.Nilpotent.GeometricallyReduced.CharZero
public import ReasLib.FieldTheory.Separable.Generated.Kaehler
public import ReasLib.FieldTheory.Separable.Generated.Kaehler.CharP
public import ReasLib.FieldTheory.Separable.Generated.OnePthRoot
public import ReasLib.FieldTheory.Separable.FormallySmooth
import StacksCheckRecall

@[expose] public section

/-!
# Characteristic-zero field extensions

Proposition 10.158.9 collects the source-facing characteristic-zero consequences while its
individual reusable owners remain in ReasLib.

@stack 0322
-/

open scoped TensorProduct

universe u v

namespace Algebra

section

variable {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]

/- Domain triage:
- `Algebra.IsSeparableOver k K`, `Algebra.IsGeometricallyReduced k K`,
  `Algebra.FormallySmooth k K`, and `Algebra.H1Cotangent k K` are the owner
  predicates for the field-extension clauses;
- the reusable Kähler criterion is
  `Algebra.IsSeparableOver.mapBaseChange_injective`, while its characteristic-`p`
  converse is `Algebra.IsSeparableOver.CharP.iff_mapBaseChange_injective`,
  applied to `KaehlerDifferential.CharP.primeFieldMapBaseChange`;
- the six-clause `List.TFAE` below remains the source-facing packaging, rather
  than becoming the shared library API.
-/

/- Proposition 10.158.9 (1), tag `0322`: canonical recall of the
characteristic-zero separability theorem for field extensions. -/
@[stacks 0322 "(1)"]
#check @Algebra.IsSeparableOver.of_charZero

/- Proposition 10.158.9 (2), tag `0322`: canonical recall of the
characteristic-zero geometric-reducedness theorem for field extensions. -/
@[stacks 0322 "(2)"]
#check @Algebra.IsGeometricallyReduced.of_charZero

/- Proposition 10.158.9 (3), tag `0322`: canonical recall of the
characteristic-zero formal-smoothness theorem for field extensions. -/
@[stacks 0322 "(3)"]
#check @Algebra.formallySmooth_of_charZero

/- Proposition 10.158.9 (4), tag `0322`: canonical recall of the
characteristic-zero vanishing theorem for first cotangent homology. -/
@[stacks 0322 "(4)"]
#check @Algebra.subsingleton_h1Cotangent_of_charZero

/- Proposition 10.158.9 (5), tag `0322`: the source takes `R = ℤ` in the
shared characteristic-zero Kähler base-change injectivity theorem. -/
@[stacks 0322 "(5)"]
#check @Algebra.IsSeparableOver.mapBaseChange_injective_of_charZero (R := ℤ)

namespace IsSeparableOver.CharP

/-- Proposition 10.158.9 (6), tag `0322`: for a field extension in
characteristic `p > 0`, the following are equivalent: Stacks-separability,
reducedness after tensoring with `k^{1/p}`, geometric reducedness, injectivity
of the prime-field Kähler base-change map, vanishing `H₁(L_{K/k})`, and formal
smoothness.  The shared library exposes the individual equivalences instead of
this order-sensitive list. -/
@[stacks 0322 "(6)"]
theorem tfae_fieldExtension
    {p : ℕ} [Fact p.Prime] [CharP k p] :
    List.TFAE [
      Algebra.IsSeparableOver k K,
      IsReduced (K ⊗[k] IntermediateField.onePthRootExtension k p),
      Algebra.IsGeometricallyReduced k K,
      Function.Injective
        (KaehlerDifferential.CharP.primeFieldMapBaseChange (R := k) (S := K) (p := p)),
      Subsingleton (Algebra.H1Cotangent k K),
      Algebra.FormallySmooth k K
    ] := sorry

end IsSeparableOver.CharP

end

end Algebra
