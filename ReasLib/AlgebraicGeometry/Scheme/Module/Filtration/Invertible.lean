/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Order.RelSeries
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Basic

/-!
# Filtrations with invertible quotients

This module records finite filtrations of scheme modules whose successive
quotients are invertible.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- A scheme module has an invertible-quotient filtration if it admits a finite filtration from
the zero subobject to the whole module and every successive cokernel quotient is invertible. -/
def HasInvertibleQuotientFiltration (E : X.Modules) : Prop :=
  ∃ s : RelSeries {FG : Subobject E × Subobject E |
      ∃ hFG : FG.1 ≤ FG.2,
        Invertible (cokernel (Subobject.ofLE FG.1 FG.2 hFG))},
    s.head = ⊥ ∧ s.last = ⊤

/-- A scheme module has an invertible-quotient filtration of length `r` if it admits a
`RelSeries` of exactly that length from the zero subobject to the whole module, with invertible
successive cokernels. -/
def HasInvertibleQuotientFiltrationOfLength (r : ℕ) (E : X.Modules) : Prop :=
  ∃ s : RelSeries {FG : Subobject E × Subobject E |
      ∃ hFG : FG.1 ≤ FG.2,
        Invertible (cokernel (Subobject.ofLE FG.1 FG.2 hFG))},
    s.length = r ∧ s.head = ⊥ ∧ s.last = ⊤

/-- A prescribed-length invertible-quotient filtration is exactly a `RelSeries` of that length
from the zero subobject to the whole module with invertible successive cokernels. -/
theorem hasInvertibleQuotientFiltrationOfLength_iff (r : ℕ) (E : X.Modules) :
    HasInvertibleQuotientFiltrationOfLength r E ↔
      ∃ s : RelSeries {FG : Subobject E × Subobject E |
          ∃ hFG : FG.1 ≤ FG.2,
            Invertible (cokernel (Subobject.ofLE FG.1 FG.2 hFG))},
        s.length = r ∧ s.head = ⊥ ∧ s.last = ⊤ := sorry

/-- Forgetting the length of a prescribed invertible-quotient filtration gives an
invertible-quotient filtration. -/
theorem HasInvertibleQuotientFiltrationOfLength.toHasInvertibleQuotientFiltration
    {r : ℕ} {E : X.Modules} (h : HasInvertibleQuotientFiltrationOfLength r E) :
    HasInvertibleQuotientFiltration E := sorry

end AlgebraicGeometry.Scheme.Modules
