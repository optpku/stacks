module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Homology.DerivedCategory.Completeness.Category
import StacksCheckRecall

/-!
# The category of derived complete modules
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace ModuleCat.DerivedComplete

section

variable {A : Type u} [CommRing A]

/- Lemma 110.11.1 (1): the category of derived complete modules is abelian. -/
@[stacks 0ARD]
#check fun (I : Ideal A) ↦ (abelian I : Abelian (category I))

/- Lemma 110.11.1 (2): the inclusion of derived complete modules into `ModuleCat A` is exact. -/
@[stacks 0ARD]
#check fun (I : Ideal A) ↦
  (inclusion_exact I : exactFunctor (category I) (ModuleCat A) (inclusion I))

/- Lemma 110.11.1 (3): the category of derived complete modules has arbitrary limits. -/
@[stacks 0ARD]
#check fun (I : Ideal A) ↦ (hasLimits I : HasLimits (category I))

/- Lemma 110.11.1 (4): the inclusion of derived complete modules commutes with arbitrary limits. -/
@[stacks 0ARD]
#check fun (I : Ideal A) ↦
  (inclusion_preservesLimits I : PreservesLimitsOfSize (inclusion I))

/- Lemma 110.11.1 (5): if `I` is finitely generated, the category of derived complete modules has
arbitrary direct sums and colimits. -/
@[stacks 0ARD]
#check fun (I : Ideal A) (hI : I.FG) ↦ (hasColimits I hI : HasColimits (category I))

end

/-- Lemma 110.11.1 (6): if `I` is finitely generated, the inclusion of derived complete modules
does not commute with colimits in general. -/
@[stacks 0ARD]
theorem exists_fg_inclusion_not_preservesColimits :
    ∃ (A : Type u) (_ : CommRing A) (I : Ideal A),
      I.FG ∧ ¬ PreservesColimits (inclusion I) := sorry

/-- The inclusion of derived complete modules does not preserve countable coproducts in general,
even when `I` is finitely generated. -/
theorem exists_fg_inclusion_not_preservesCoproducts :
    ∃ (A : Type u) (_ : CommRing A) (I : Ideal A),
      I.FG ∧ ¬ PreservesColimitsOfShape (Discrete ℕ) (inclusion I) := sorry

/-- Lemma 110.11.1 (7): filtered colimits are not exact in the category of derived complete
modules in general. -/
@[stacks 0ARD]
theorem exists_fg_not_hasExactColimitsOfShape_nat :
    ∃ (A : Type u) (_ : CommRing A) (I : Ideal A),
      I.FG ∧ ∀ [HasColimitsOfShape ℕ (category I)],
        ¬ Nonempty (HasExactColimitsOfShape ℕ (category I)) := sorry

/-- Lemma 110.11.1 (8): the category of derived complete modules is not a Grothendieck abelian
category in general. -/
@[stacks 0ARD]
theorem exists_fg_not_isGrothendieckAbelian :
    ∃ (A : Type u) (_ : CommRing A) (I : Ideal A),
      I.FG ∧ ¬ IsGrothendieckAbelian (category I) := sorry

end ModuleCat.DerivedComplete
