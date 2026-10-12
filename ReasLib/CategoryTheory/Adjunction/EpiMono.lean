/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import Mathlib.CategoryTheory.Functor.EpiMono
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Balanced
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Epimorphism criteria for adjunctions

This file isolates the epi/reflection part of an adjunction.  It is independent
of sites and topoi, so site-specific applications should import this leaf
instead of re-proving the counit argument.
-/

@[expose] public section

open CategoryTheory

universe vC vD uC uD

namespace CategoryTheory.Adjunction

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]
variable {L : C ⥤ D} {R : D ⥤ C}

/-- Explicit-evidence form of Mathlib's faithful-right-adjoint criterion for
epic counit components. -/
theorem faithful_R_of_counit_epi
    (adj : L ⊣ R)
    (h_counit : ∀ X : D, Epi (adj.counit.app X)) :
    R.Faithful := sorry

/-- Epic components of the counit of an adjunction force its right adjoint to
reflect epimorphisms. -/
theorem reflectsEpimorphisms_of_counit_epi
    (adj : L ⊣ R)
    (h_counit : ∀ X : D, Epi (adj.counit.app X)) :
    R.ReflectsEpimorphisms := sorry

/-- If the right adjoint of an adjunction reflects epimorphisms, every counit
component is epic. -/
theorem counit_epi_of_reflectsEpimorphisms
    (adj : L ⊣ R)
    (h_reflects : R.ReflectsEpimorphisms) :
    ∀ X : D, Epi (adj.counit.app X) := sorry

/-- The right adjoint of an adjunction reflects epimorphisms exactly when all components of its
counit are epic. -/
@[stacks 04DA "counit criterion"]
theorem counit_epi_iff_reflectsEpimorphisms
    (adj : L ⊣ R) :
    (∀ X : D, Epi (adj.counit.app X)) ↔ R.ReflectsEpimorphisms := sorry

/-- Explicit-adjunction form of the fact that a right adjoint which reflects epimorphisms is
faithful. -/
theorem faithful_R_of_reflectsEpimorphisms
    (adj : L ⊣ R)
    (h_reflects : R.ReflectsEpimorphisms) :
    R.Faithful := sorry

/-- A right adjoint which reflects epimorphisms also reflects monomorphisms. -/
theorem reflectsMonomorphisms_R_of_reflectsEpimorphisms
    (adj : L ⊣ R)
    (h_reflects : R.ReflectsEpimorphisms) :
    R.ReflectsMonomorphisms := sorry

/-- In a balanced target category, a right adjoint which reflects
epimorphisms reflects isomorphisms. -/
theorem reflectsIsomorphisms_R_of_reflectsEpimorphisms
    (adj : L ⊣ R) [Balanced D]
    (h_reflects : R.ReflectsEpimorphisms) :
    R.ReflectsIsomorphisms := sorry

end CategoryTheory.Adjunction

namespace CategoryTheory.Functor

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]

/-- A right adjoint which reflects epimorphisms is faithful. This form uses the canonical
`IsRightAdjoint` and `ReflectsEpimorphisms` owners and does not force downstream users to name a
left adjoint or reflection witness. -/
@[stacks 04DA "faithfulness"]
theorem faithful_of_reflectsEpimorphisms
    (R : D ⥤ C) [R.IsRightAdjoint] [R.ReflectsEpimorphisms] :
    R.Faithful := sorry

end CategoryTheory.Functor
