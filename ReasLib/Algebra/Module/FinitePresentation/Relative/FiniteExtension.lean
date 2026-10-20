/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.FinitePresentation.RestrictScalars
public import ReasLib.Algebra.Module.FinitePresentation.Relative.Presentation
import Mathlib.Tactic.CrossRefAttribute

/-!
# Relative finite presentation across finite extensions

@stack 05H0

For a finite map of finite-type algebras, relative finite presentation can be tested over either
the source algebra or the target algebra.
-/

@[expose] public section

universe u v w x

namespace Module

variable {R : Type u} {A : Type v} {B : Type w} {M : Type x}
variable [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
variable [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]
variable [Algebra.FiniteType R A] [Module.Finite A B]

/-- Lemma 15.81.3 (05H0): finite scalar extension preserves and reflects relative finite
presentation of a module. -/
@[stacks 05H0 "finite extension and relative finite presentation"]
theorem finitePresentationRelativeTo_iff_of_finite :
    FinitePresentationRelativeTo R A M ↔ FinitePresentationRelativeTo R B M := sorry
/- Proof strategy: use the presentation-independent characterization over `R`; for each chosen
polynomial presentation, apply `Module.FinitePresentation.iff_restrictScalars_of_finite` to the
compatible `A`- and `B`-module structures, using finiteness of `B/A` and the induced finite
presentation of the scalar extension. -/

end Module
