/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.SmallAcyclic.Bounds
public import ReasLib.Algebra.Homology.HomotopyCategory.KInjective.Characterization
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Detecting K-Injective Complexes on Small Acyclic Sources

In a locally small, well-powered abelian category with exact filtered colimits, a uniform
supply of small acyclic subcomplexes reduces K-injectivity of a termwise injective complex
to vanishing against the corresponding bounded-above test complexes.  The intermediate
API separates test-family vanishing, chain-level null-homotopy, and the canonical right-orthogonal
characterization of K-injectivity.
-/

open CategoryTheory
open ComplexShape

universe z w v u

namespace CochainComplex.SmallAcyclic

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- Vanishing in the homotopy category against all bounded-above acyclic complexes controlled
by `kappa`. -/
@[stacks 079L "small acyclic test vanishing"]
def HomotopyVanishing (kappa : Cardinal.{z})
    (I : CochainComplex A ℤ) : Prop :=
  ∀ (M : CochainComplex A ℤ) (_ : BoundedBy kappa M)
    (f : (HomotopyCategory.quotient A (up ℤ)).obj M ⟶
      (HomotopyCategory.quotient A (up ℤ)).obj I), f = 0

namespace HomotopyVanishing

variable {kappa : Cardinal.{z}} {I : CochainComplex A ℤ}

/-- A homotopy-category morphism from a small acyclic test complex vanishes. -/
theorem eq_zero (h : HomotopyVanishing kappa I) {M : CochainComplex A ℤ}
    (hM : BoundedBy kappa M)
    (f : (HomotopyCategory.quotient A (up ℤ)).obj M ⟶
      (HomotopyCategory.quotient A (up ℤ)).obj I) :
    f = 0 := sorry

/-- Test-family vanishing applies to every shift of a small acyclic source. -/
theorem shift (h : HomotopyVanishing kappa I) {M : CochainComplex A ℤ}
    (hM : BoundedBy kappa M) (n : ℤ)
    (f : (HomotopyCategory.quotient A (up ℤ)).obj (M⟦n⟧) ⟶
      (HomotopyCategory.quotient A (up ℤ)).obj I) :
    f = 0 := sorry

/-- Test-family vanishing makes every chain map from a small acyclic source null-homotopic. -/
theorem nullHomotopic (h : HomotopyVanishing kappa I) {M : CochainComplex A ℤ}
    (hM : BoundedBy kappa M) (f : M ⟶ I) :
    Nonempty (Homotopy f 0) := sorry

/-- If every nonzero acyclic complex contains a small acyclic test complex, then test-family
vanishing against a termwise injective target makes every map from an acyclic source
null-homotopic. Exact filtered colimits form the acyclic limit stages; local smallness and
well-poweredness at the same universe bound the subobjects and force exhaustion. No separator
is required once the small-subcomplex supply is given. -/
theorem nullHomotopicOfAcyclic
    [LocallySmall.{w} A] [Limits.HasFilteredColimitsOfSize.{w, w} A]
    [AB5OfSize.{w, w} A] [WellPowered.{w} A] (h : HomotopyVanishing kappa I)
    (hsub : HasSubcomplexes A kappa) [∀ j : ℤ, Injective (I.X j)]
    {M : CochainComplex A ℤ} (hM : M.Acyclic) (f : M ⟶ I) :
    Nonempty (Homotopy f 0) := sorry

/-- A uniform small-acyclic-subcomplex bound promotes test-family vanishing to the canonical
right-orthogonality of the target to all acyclic homotopy objects, using exact filtered unions
and well-poweredness in a common universe. -/
theorem rightOrthogonal
    [LocallySmall.{w} A] [Limits.HasFilteredColimitsOfSize.{w, w} A]
    [AB5OfSize.{w, w} A] [WellPowered.{w} A] (h : HomotopyVanishing kappa I)
    (hsub : HasSubcomplexes A kappa) [∀ j : ℤ, Injective (I.X j)] :
    (HomotopyCategory.subcategoryAcyclic A).rightOrthogonal
      ((HomotopyCategory.quotient A (up ℤ)).obj I) := sorry

end HomotopyVanishing
end CochainComplex.SmallAcyclic

namespace CochainComplex.IsKInjective

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- Lemma 19.12.3: a termwise injective complex is K-injective when one uniform cardinal
supplies small acyclic subcomplexes and all homotopy-category morphisms from the corresponding
bounded-above acyclic test complexes vanish. The exact filtered-colimit and well-poweredness
hypotheses are the components of the Grothendieck assumption used in the reduction argument;
the Grothendieck source case supplies them automatically. -/
@[stacks 079L "small acyclic detection"]
theorem ofSmallAcyclic
    [LocallySmall.{w} A] [Limits.HasFilteredColimitsOfSize.{w, w} A]
    [AB5OfSize.{w, w} A] [WellPowered.{w} A] (I : CochainComplex A ℤ) [∀ j : ℤ, Injective (I.X j)]
    (kappa : Cardinal.{z})
    (hsub : SmallAcyclic.HasSubcomplexes A kappa)
    (hvanish : SmallAcyclic.HomotopyVanishing kappa I) :
    I.IsKInjective := sorry

end CochainComplex.IsKInjective
