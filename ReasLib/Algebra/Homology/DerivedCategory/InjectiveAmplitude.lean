/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat
public import ReasLib.CategoryTheory.DerivedCategory.InjectiveAmplitude
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Injective amplitude of derived module complexes

@stack 0A5S

The generic owner is `CategoryTheory.DerivedCategory`.  This leaf retains the historical
Chapter 15 spellings for derived module complexes while delegating all definitions and closure
API to the category-level object properties.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace CategoryTheory

variable {R : Type u} [Ring R]

/-- A derived module complex has injective amplitude in `[a, b]` when it is represented by
a complex of injective modules supported in that interval. -/
@[stacks 0A5S "(2), module-category specialization"]
abbrev HasInjectiveAmplitudeIn
    (K : DerivedCategory (ModuleCat R)) (a b : ℤ) : Prop :=
  DerivedCategory.HasInjectiveAmplitudeIn K a b

/-- A derived module complex has finite injective dimension when it has injective amplitude
in some finite interval. -/
@[stacks 0A5S "(1), module-category specialization"]
abbrev HasFiniteInjectiveDimension (K : DerivedCategory (ModuleCat R)) : Prop :=
  DerivedCategory.HasFiniteInjectiveDimension K

/-- The module specialization may be unpacked to an ordinary cochain complex with explicit
support and injectivity conditions. -/
@[stacks 0A5S "injective-amplitude representative"]
theorem hasInjectiveAmplitudeIn_iff_exists_representative
    (K : DerivedCategory (ModuleCat R)) (a b : ℤ) :
    HasInjectiveAmplitudeIn K a b ↔
      ∃ I : CochainComplex (ModuleCat R) ℤ,
        I.IsStrictlyGE a ∧ I.IsStrictlyLE b ∧
          (∀ i : ℤ, Injective (I.X i)) ∧ Nonempty (K ≅ DerivedCategory.Q.obj I) := sorry

/-- The module specialization has finite injective dimension exactly when it belongs to one
injective-amplitude interval. -/
@[stacks 0A5S "finite injective dimension criterion"]
theorem hasFiniteInjectiveDimension_iff
    (K : DerivedCategory (ModuleCat R)) :
    HasFiniteInjectiveDimension K ↔
      ∃ a b : ℤ, HasInjectiveAmplitudeIn K a b := sorry

end CategoryTheory
