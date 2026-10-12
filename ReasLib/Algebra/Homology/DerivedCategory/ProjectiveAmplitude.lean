/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat
public import ReasLib.Algebra.Homology.CochainComplex.Projective.Bounded.KProjective
public import ReasLib.Algebra.Homology.CochainComplex.Projective.Bounded.Minus
public import ReasLib.CategoryTheory.DerivedCategory.ProjectiveAmplitude
import Mathlib.Tactic.CrossRefAttribute

/-!
# Projective amplitude of derived module complexes

@stack 0A5N

The generic owner is `CategoryTheory.DerivedCategory`.  This leaf keeps the historical Chapter 15
spellings for `D(R)` while exposing the raw representative formulation used by existing consumers
and the bundled representative view for new developments.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace CategoryTheory

variable {R : Type u} [Ring R]

/-- Definition 15.69.1 (2), tag `0A5N`: projective amplitude in `[a, b]` for `D(R)`. -/
@[stacks 0A5N "module-category projective amplitude"]
abbrev HasProjectiveAmplitudeIn
    (K : DerivedCategory (ModuleCat R)) (a b : ℤ) : Prop :=
  DerivedCategory.HasProjectiveAmplitudeIn K a b

/-- Definition 15.69.1 (1), tag `0A5N`: finite projective dimension for `D(R)`. -/
@[stacks 0A5N "module-category finite projective dimension"]
abbrev HasFiniteProjectiveDimension
    (K : DerivedCategory (ModuleCat R)) : Prop :=
  DerivedCategory.HasFiniteProjectiveDimension K

/-- The module specialization may be unpacked to an ordinary cochain complex with explicit support
and termwise projectivity. -/
@[stacks 0A5N "module projective amplitude representative bridge"]
theorem hasProjectiveAmplitudeIn_iff_exists_representative
    (K : DerivedCategory (ModuleCat R)) (a b : ℤ) :
    HasProjectiveAmplitudeIn K a b ↔
      ∃ (P : CochainComplex (ModuleCat R) ℤ) (_ : K ≅ DerivedCategory.Q.obj P),
        P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧ ∀ i : ℤ, Projective (P.X i) := sorry

/-- The module specialization also exposes the bundled bounded-projective representative owner. -/
@[stacks 0A5N "module bundled projective amplitude bridge"]
theorem hasProjectiveAmplitudeIn_iff_exists_bundled
    (K : DerivedCategory (ModuleCat R)) (a b : ℤ) :
    HasProjectiveAmplitudeIn K a b ↔
      ∃ (P : CochainComplex.ProjectiveIn (ModuleCat R) a b),
        Nonempty (K ≅ DerivedCategory.Q.obj P.obj) := sorry

/-- Finite projective dimension is the existence of one finite projective-amplitude interval. -/
@[stacks 0A5N "module finite projective dimension interval bridge"]
theorem hasFiniteProjectiveDimension_iff
    (K : DerivedCategory (ModuleCat R)) :
    HasFiniteProjectiveDimension K ↔
      ∃ a b : ℤ, HasProjectiveAmplitudeIn K a b := sorry

end CategoryTheory
