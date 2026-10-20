module

public import ReasLib.Algebra.Homology.DerivedCategory.Completeness.CategoryCounterexample
import StacksCheckRecall

/-!
# The category of derived complete modules
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

/- Lemma 110.11.1 (1): the category of derived complete modules is abelian. -/
@[stacks 0ARD]
#check (ModuleCat.DerivedComplete.abelian :
  ∀ {A : Type u} [CommRing A] (I : Ideal A), Abelian (ModuleCat.DerivedComplete.category I))

/- Lemma 110.11.1 (2): the inclusion of derived complete modules into `ModuleCat A` is exact. -/
@[stacks 0ARD]
#check (ModuleCat.DerivedComplete.inclusion_exact :
  ∀ {A : Type u} [CommRing A] (I : Ideal A),
    exactFunctor (ModuleCat.DerivedComplete.category I) (ModuleCat A)
      (ModuleCat.DerivedComplete.inclusion I))

/- Lemma 110.11.1 (3): the category of derived complete modules has arbitrary limits. -/
@[stacks 0ARD]
#check (ModuleCat.DerivedComplete.hasLimits :
  ∀ {A : Type u} [CommRing A] (I : Ideal A), HasLimits (ModuleCat.DerivedComplete.category I))

/- Lemma 110.11.1 (4): the inclusion of derived complete modules commutes with arbitrary limits. -/
@[stacks 0ARD]
#check (ModuleCat.DerivedComplete.inclusion_preservesLimits :
  ∀ {A : Type u} [CommRing A] (I : Ideal A),
    PreservesLimitsOfSize (ModuleCat.DerivedComplete.inclusion I))

/- Lemma 110.11.1 (5): if `I` is finitely generated, the category of derived complete modules has
arbitrary direct sums and colimits. -/
@[stacks 0ARD]
#check (ModuleCat.DerivedComplete.hasColimits :
  ∀ {A : Type u} [CommRing A] (I : Ideal A),
    I.FG → HasColimits (ModuleCat.DerivedComplete.category I))

/- Lemma 110.11.1 (6): the finitely generated ideal `(p)` in `ℤ_[p]` gives a derived-complete
module inclusion that does not preserve all colimits. -/
@[stacks 0ARD]
#check (ModuleCat.DerivedComplete.padic_inclusion_not_preservesColimits :
  ∀ (p : ℕ) [Fact p.Prime], (principalIdeal (p : ℤ_[p])).FG ∧
    ¬ PreservesColimits (ModuleCat.DerivedComplete.inclusion (principalIdeal (p : ℤ_[p]))))

/- Lemma 110.11.1 (7): the inclusion does not preserve countable direct sums for `(p)` in `ℤ_[p]`. -/
@[stacks 0ARD]
#check (ModuleCat.DerivedComplete.padic_inclusion_not_preservesCoproducts :
  ∀ (p : ℕ) [Fact p.Prime], (principalIdeal (p : ℤ_[p])).FG ∧
    ¬ PreservesColimitsOfShape (Discrete ℕ)
      (ModuleCat.DerivedComplete.inclusion (principalIdeal (p : ℤ_[p]))))

/- Lemma 110.11.1 (8): sequential filtered colimits in the derived-complete category for `(p)`
in `ℤ_[p]` are not exact. -/
@[stacks 0ARD]
#check (ModuleCat.DerivedComplete.padic_not_hasExactColimitsOfShape_nat :
  ∀ (p : ℕ) [Fact p.Prime], (principalIdeal (p : ℤ_[p])).FG ∧
    ∀ [HasColimitsOfShape ℕ
      (ModuleCat.DerivedComplete.category (principalIdeal (p : ℤ_[p])))],
      ¬ Nonempty (HasExactColimitsOfShape ℕ
        (ModuleCat.DerivedComplete.category (principalIdeal (p : ℤ_[p])))))

/- Lemma 110.11.1 (9): this derived-complete category is not Grothendieck abelian. -/
@[stacks 0ARD]
#check (ModuleCat.DerivedComplete.padic_not_isGrothendieckAbelian :
  ∀ (p : ℕ) [Fact p.Prime], (principalIdeal (p : ℤ_[p])).FG ∧
    ¬ IsGrothendieckAbelian
      (ModuleCat.DerivedComplete.category (principalIdeal (p : ℤ_[p]))))
