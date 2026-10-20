/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Abelian.Projective.Dimension
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Depth

/-!
# The Auslander--Buchsbaum Formula

@stack 090V

This leaf owns the relation between depth and finite projective dimension for
finite nonzero modules over Noetherian local rings.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace Module

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- The Auslander--Buchsbaum formula with an explicit natural projective-dimension value. -/
@[stacks 090V "Auslander--Buchsbaum formula with explicit projective dimension"]
theorem auslanderBuchsbaum {d : ℕ}
    (hpd : projectiveDimension (ModuleCat.of R M) = d) :
    moduleDepth R R = d + moduleDepth R M := sorry

/-- Finite projective dimension of a finite nonzero module has a natural value satisfying the
Auslander--Buchsbaum formula. -/
@[stacks 090V "finite-projective-dimension Auslander--Buchsbaum formula"]
theorem exists_auslanderBuchsbaum [Nontrivial M]
    (h_finite : projectiveDimension (ModuleCat.of R M) ≠ ⊤) :
    ∃ d : ℕ,
      projectiveDimension (ModuleCat.of R M) = d ∧
        moduleDepth R R = d + moduleDepth R M := sorry

end Module
