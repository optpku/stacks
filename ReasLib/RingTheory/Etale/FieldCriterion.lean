/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Etale.Field
public import Mathlib.Data.List.TFAE
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# The Kähler-differential criterion for etale algebras over fields

The field criterion is stated at the algebra owner level.  The `EssFiniteType`
assumption is the natural Mathlib generalization of the finite-type wording of
the source item; the converse uses the finite module consequence of formal
unramifiedness over a field to recover finite presentation.

@stack 090W
-/

universe u v

namespace Algebra.Etale

variable {k : Type u} {S : Type v}
variable [Field k] [CommRing S] [Algebra k S] [EssFiniteType k S]

/-- Lemma 10.143.3 (00U2), clause (7): over a field, an essentially finite
type algebra is etale exactly when its module of Kähler differentials is
subsingleton. -/
@[stacks 00U2 "etale criterion by Kahler differentials over a field"]
theorem iff_subsingleton_kaehlerDifferential :
    Algebra.Etale k S ↔ Subsingleton Ω[S⁄k] := sorry

end Algebra.Etale

namespace Algebra.Separable.FieldExtension

variable {k : Type u} {K : Type v}
variable [Field k] [Field K] [Algebra k K] [Algebra.EssFiniteType k K]

/-- The six equivalent field-extension criteria: finite separability, vanishing
Kähler differentials, formal unramifiedness, unramifiedness, formal etaleness,
and etaleness. -/
theorem tfae :
    List.TFAE [
      FiniteDimensional k K ∧ Algebra.IsSeparable k K,
      Subsingleton Ω[K⁄k],
      Algebra.FormallyUnramified k K,
      Algebra.Unramified k K,
      Algebra.FormallyEtale k K,
      Algebra.Etale k K
    ] := sorry

end Algebra.Separable.FieldExtension
