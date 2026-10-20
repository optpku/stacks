/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Ideal.LocallyNilpotent
public import ReasLib.RingTheory.Finiteness.Projective

/-!
# Projective modules across nilpotent quotient rings

This leaf owns the existence theorems for lifting projective modules from a quotient ring.  They
are stated directly in terms of the quotient module `Pbar ⧸ I Pbar`, independently of a chosen
free cover or idempotent presentation.
-/

@[expose] public section

universe u v

namespace Module.Projective

section General

variable {R : Type u} [Ring R]
variable {I : Ideal R} [I.IsTwoSided]
variable {Pbar : Type v} [AddCommGroup Pbar] [Module (R ⧸ I) Pbar]

/-- Lemma 10.77.5 (07LV): a projective module over `R ⧸ I` lifts across a nilpotent two-sided
ideal to a projective `R`-module, with an explicit quotient comparison. -/
@[stacks 07LV "projective lift across a nilpotent quotient"]
theorem exists_lift_of_isNilpotent
    (hI : IsNilpotent I) (hPbar : Module.Projective (R ⧸ I) Pbar) :
    ∃ (P : Type (max u v)) (_ : AddCommGroup P) (_ : Module R P)
      (_ : (P ⧸ (I • (⊤ : Submodule R P))) ≃ₗ[R ⧸ I] Pbar), Module.Projective R P := sorry

end General

section Commutative

variable {R : Type u} [CommRing R]
variable {I : Ideal R}
variable {Pbar : Type v} [AddCommGroup Pbar] [Module (R ⧸ I) Pbar]

/-- Lemma 10.77.6 (0D47): a finite projective module over a locally nilpotent quotient lifts to
a finite projective module over the original commutative ring, with the quotient equivalence
available as a direct witness. -/
@[stacks 0D47 "finite projective lift across a locally nilpotent quotient"]
theorem exists_finite_lift_of_isLocallyNilpotent
    [Module.Finite (R ⧸ I) Pbar] [Module.Projective (R ⧸ I) Pbar]
    (hI : I.IsLocallyNilpotent) :
    ∃ (P : Type u) (_ : AddCommGroup P) (_ : Module R P)
      (e : (P ⧸ (I • (⊤ : Submodule R P))) ≃ₗ[R ⧸ I] Pbar),
      Module.FiniteProjective R P := sorry

end Commutative

end Module.Projective
