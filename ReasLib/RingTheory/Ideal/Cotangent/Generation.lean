/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Generators of an Ideal and Its Cotangent Module

@stack 00SC

This leaf compares a specified family of elements of an ideal with its images
in the conormal module `I.Cotangent = I / I^2`.  The Jacobson-radical
converse is a direct reusable form of Nakayama's lemma.
-/

universe u v

namespace Ideal.Cotangent

variable {R : Type u} [CommRing R] {I : Ideal R}

/-- If a family generates an ideal, then its images generate the cotangent module `I / I²`. -/
@[stacks 00SC "ideal generators induce cotangent generators"]
theorem span_toCotangent_eq_top_of_ideal_span_eq
    {ι : Type v} (xs : ι → I)
    (hxs : Ideal.span (Set.range fun i => (xs i : R)) = I) :
    Submodule.span (R ⧸ I) (Set.range fun i => I.toCotangent (xs i)) = ⊤ := sorry

/-- Nakayama lifts a cotangent-generating family in a Jacobson-radical ideal to generators of
the ideal itself.

Only finite generation of `I` as an `R`-module is needed; no Noetherian or local-ring
assumption belongs to this general statement. -/
@[stacks 00SC "cotangent generators lift by Nakayama"]
theorem ideal_span_eq_of_span_toCotangent_eq_top
    [Module.Finite R I] (hIjac : I ≤ Ring.jacobson R)
    {ι : Type v} (xs : ι → I)
    (hxs : Submodule.span (R ⧸ I) (Set.range fun i => I.toCotangent (xs i)) = ⊤) :
    Ideal.span (Set.range fun i => (xs i : R)) = I := sorry

/-- A generating family of `I / I²` has lifts which generate a finitely generated ideal in the
Jacobson radical.

The conclusion remembers that each chosen lift has the prescribed cotangent image, so it can be
used to transport statements about a specified family rather than merely its cardinality. -/
@[stacks 00SC "cotangent generators admit ideal-generator lifts"]
theorem exists_lift_generators_of_span_eq_top
    [Module.Finite R I] (hIjac : I ≤ Ring.jacobson R)
    {ι : Type v} (xs : ι → I.Cotangent)
    (hxs : Submodule.span (R ⧸ I) (Set.range xs) = ⊤) :
    ∃ ys : ι → I,
      (∀ i, I.toCotangent (ys i) = xs i) ∧
        Ideal.span (Set.range fun i => (ys i : R)) = I := sorry

/-- A finitely generated ideal in the Jacobson radical has an `ι`-indexed family of elements of
the ambient ring generating it exactly when its cotangent module has an `ι`-indexed generating
family.

The ambient-ring family is the natural public form of ideal generation: membership in `I` follows
from the displayed span equality, while callers need not manufacture subtype terms first. -/
@[stacks 00SC "existence of ideal and cotangent generating families"]
theorem exists_generators_iff_exists_cotangent_generators
    [Module.Finite R I] (hIjac : I ≤ Ring.jacobson R) {ι : Type v} :
    (∃ xs : ι → R, Ideal.span (Set.range xs) = I) ↔
      ∃ xs : ι → I.Cotangent,
        Submodule.span (R ⧸ I) (Set.range xs) = ⊤ := sorry

/-- A finitely generated ideal in the Jacobson radical has an `ι`-indexed generating family of
elements already bundled in the ideal exactly when its cotangent module has one.

This subtype form is useful when a construction needs the chosen generators as elements of `I`,
for example to prescribe their cotangent images. -/
@[stacks 00SC "subtype ideal and cotangent generating families"]
theorem exists_subtype_generators_iff_exists_cotangent_generators
    [Module.Finite R I] (hIjac : I ≤ Ring.jacobson R) {ι : Type v} :
    (∃ xs : ι → I, Ideal.span (Set.range fun i => (xs i : R)) = I) ↔
      ∃ xs : ι → I.Cotangent,
        Submodule.span (R ⧸ I) (Set.range xs) = ⊤ := sorry

/-- For a finitely generated ideal in the Jacobson radical, a specified family generates the
ideal exactly when its images generate `I / I²`. -/
@[stacks 00SC "ideal and cotangent generation criterion"]
theorem ideal_span_eq_iff_span_toCotangent_eq_top
    [Module.Finite R I] (hIjac : I ≤ Ring.jacobson R)
    {ι : Type v} (xs : ι → I) :
    Ideal.span (Set.range fun i => (xs i : R)) = I ↔
      Submodule.span (R ⧸ I) (Set.range fun i => I.toCotangent (xs i)) = ⊤ := sorry

end Ideal.Cotangent
