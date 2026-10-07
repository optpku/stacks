module

public import Mathlib.RingTheory.Localization.Away.AdjoinRoot
public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.Localization
public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.Relative.Tensor
import Mathlib.Tactic.CrossRefAttribute

/-!
# Localization of relative pseudo-coherence

Relative pseudo-coherence is preserved when localizing a finite-type algebra, and it can be
detected on a finite principal-open cover.

@stack 0679
@stack 067E
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u v w

namespace CategoryTheory.DerivedCategory.IsMPseudoCoherentRelativeTo

/-- Lemma 15.82.11 (1): localizing an algebra over a localized finite-type base preserves
relative `m`-pseudo-coherence after returning to the original base. -/
@[stacks 0679 "(1), localization from a localized base"]
theorem localizationAway_from_localizedBase
    {R : Type u} {A : Type v} [CommRing R] [CommRing A]
    (f : R) [Algebra R A] [Algebra (Localization.Away f) A]
    [IsScalarTower R (Localization.Away f) A]
    [Algebra.FiniteType (Localization.Away f) A]
    (g : A) {K : DerivedCategory (ModuleCat A)} {m : ℤ}
    (hK : K.IsMPseudoCoherentRelativeTo (Localization.Away f) m) :
    let _ : Algebra.FiniteType R A :=
      Algebra.FiniteType.trans
        (inferInstance : Algebra.FiniteType R (Localization.Away f))
        (inferInstance : Algebra.FiniteType (Localization.Away f) A)
    let _ : Algebra.FiniteType R (Localization.Away g) :=
      Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType R A)
        (inferInstance : Algebra.FiniteType A (Localization.Away g))
    ((ModuleCat.derivedExtensionOfScalars
      (algebraMap A (Localization.Away g))).obj K).IsMPseudoCoherentRelativeTo R m := sorry

/-- Lemma 15.82.16 (1): relative `m`-pseudo-coherence is detected on a finite principal-open
cover of a finite-type algebra. -/
@[stacks 067E "(1), relative m-pseudo-coherence on a principal-open cover"]
theorem localizationAway_unitIdeal_iff
    {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.FiniteType R A] {ι : Type w} [Finite ι]
    (f : ι → A) (hunit : Ideal.span (Set.range f) = ⊤)
    (K : DerivedCategory (ModuleCat A)) (m : ℤ) :
    (∀ i, ((ModuleCat.derivedExtensionOfScalars
      (algebraMap A (Localization.Away (f i)))).obj K).IsMPseudoCoherentRelativeTo R m) ↔
      K.IsMPseudoCoherentRelativeTo R m := sorry

end CategoryTheory.DerivedCategory.IsMPseudoCoherentRelativeTo

namespace CategoryTheory.DerivedCategory.IsPseudoCoherentRelativeTo

/-- Lemma 15.82.11 (2): localizing an algebra over a localized finite-type base preserves
relative pseudo-coherence after returning to the original base. -/
@[stacks 0679 "(2), localization from a localized base"]
theorem localizationAway_from_localizedBase
    {R : Type u} {A : Type v} [CommRing R] [CommRing A]
    (f : R) [Algebra R A] [Algebra (Localization.Away f) A]
    [IsScalarTower R (Localization.Away f) A]
    [Algebra.FiniteType (Localization.Away f) A]
    (g : A) {K : DerivedCategory (ModuleCat A)}
    (hK : K.IsPseudoCoherentRelativeTo (Localization.Away f)) :
    let _ : Algebra.FiniteType R A :=
      Algebra.FiniteType.trans
        (inferInstance : Algebra.FiniteType R (Localization.Away f))
        (inferInstance : Algebra.FiniteType (Localization.Away f) A)
    let _ : Algebra.FiniteType R (Localization.Away g) :=
      Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType R A)
        (inferInstance : Algebra.FiniteType A (Localization.Away g))
    ((ModuleCat.derivedExtensionOfScalars
      (algebraMap A (Localization.Away g))).obj K).IsPseudoCoherentRelativeTo R := sorry

/-- Lemma 15.82.16 (2): relative pseudo-coherence is detected on a finite principal-open cover
of a finite-type algebra. -/
@[stacks 067E "(2), relative pseudo-coherence on a principal-open cover"]
theorem localizationAway_unitIdeal_iff
    {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.FiniteType R A] {ι : Type w} [Finite ι]
    (f : ι → A) (hunit : Ideal.span (Set.range f) = ⊤)
    (K : DerivedCategory (ModuleCat A)) :
    (∀ i, ((ModuleCat.derivedExtensionOfScalars
      (algebraMap A (Localization.Away (f i)))).obj K).IsPseudoCoherentRelativeTo R) ↔
      K.IsPseudoCoherentRelativeTo R := sorry

end CategoryTheory.DerivedCategory.IsPseudoCoherentRelativeTo
