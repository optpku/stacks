/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.FieldTheory.Frobenius.Compositum
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Order.Directed
import Mathlib.Tactic.CrossRefAttribute

/-!
# Frobenius composita in finite extensions

@stack 07P4

The finite-extension intersection statement is expressed in the lattice of subfields.  This is
the reusable surface; the chapter's `IntermediateField` spelling is only a compatibility view.
-/

@[expose] public section

universe u v w

namespace FieldExtension.Frobenius

variable {p : ℕ}
variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]

section DirectedIntersection

variable [Fact p.Prime] [CharP K p] [CharP L p] [FiniteDimensional K L]

/-- Lemma 15.46.4 (2): in a finite extension, Frobenius commutes with a directed subfield
intersection after adjoining the scalar-extended base fields. -/
@[stacks 07P4 "Lemma 15.46.4 (2): finite-extension Frobenius intersection"]
theorem subfield_eq_iInf_compositumMap {A : Type w} (Kα : A → Subfield K)
    (h_inter : subfield p K = ⨅ α, Kα α)
    (h_directed : Directed (· ≥ ·) Kα) :
    subfield p L = ⨅ α, compositumMap p (Kα α) := sorry
/- Proof strategy: use the finite-dimensional Frobenius descent argument, with `Subfield.map` and
`Subfield.map_sup` as the tower comparison API; the reverse inclusion is the only deferred proof. -/

/-- The finite-extension intersection in the `IntermediateField` presentation. -/
@[stacks 07P4 "Lemma 15.46.4 (2): IntermediateField presentation"]
theorem subfield_eq_iInf_compositum_toSubfield {A : Type w} (Kα : A → Subfield K)
    (h_inter : subfield p K = ⨅ α, Kα α)
    (h_directed : Directed (· ≥ ·) Kα) :
    subfield p L =
      ⨅ α, (compositum p ((Kα α).map (algebraMap K L)) L).toSubfield := sorry
/- Proof strategy: rewrite each term with `compositum_toSubfield_eq_compositumMap` and apply
`subfield_eq_iInf_compositumMap`; no chapter-specific intermediate fields are needed. -/

end DirectedIntersection

end FieldExtension.Frobenius
