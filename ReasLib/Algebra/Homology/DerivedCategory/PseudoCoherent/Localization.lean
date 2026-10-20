module

public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.PseudoCoherent
import ReasLib.Algebra.Module.LocalizedModule.Away.Cover

@[expose] public section

/-!
# Pseudo-coherence on principal-open covers

@stack 066D

Pseudo-coherence of a derived module can be checked after localizing on principal opens whose
denominators generate the unit ideal.  The reusable API is indexed by a set of denominators,
matching Mathlib's `of_localizationSpan` interfaces; the finite-family presentation lives in the
`Localization.FiniteFamily` companion leaf.  The commutative-ring assumption is the canonical
project model for principal-open localization and the symmetric derived tensor used by the Stacks
statement.
-/

open CategoryTheory

noncomputable section

universe u v

namespace CategoryTheory.DerivedCategory.IsMPseudoCoherent

variable {R : Type u} [CommRing R]

/-- Tag 066D: `m`-pseudo-coherence descends from a principal-open cover. -/
@[stacks 066D "m-pseudo-coherence on a principal-open cover"]
theorem of_localizationSpan (s : Set R) (hs : Ideal.span s = ⊤)
    {K : DerivedCategory (ModuleCat.{v, u} R)} {m : ℤ}
    (hK : ∀ f : s,
      ((ModuleCat.derivedExtensionOfScalars
        (algebraMap R (Localization.Away f.1))).obj K).IsMPseudoCoherent m) :
    K.IsMPseudoCoherent m := sorry
-- Proof strategy: descend homology vanishing and finite presentation from the localizations using
-- `Module.subsingleton_of_localizationSpan` and `Module.FinitePresentation.of_localizationSpan`,
-- then induct on the highest nonzero homology degree by attaching a finite free approximation and
-- applying the triangulated stability of `IsMPseudoCoherent` to its cone.

/-- Tag 066D: `m`-pseudo-coherence is local on a principal-open cover. -/
@[stacks 066D "m-pseudo-coherence is principal-open local"]
theorem iff_localizationSpan (s : Set R) (hs : Ideal.span s = ⊤)
    (K : DerivedCategory (ModuleCat.{v, u} R)) (m : ℤ) :
    K.IsMPseudoCoherent m ↔
      ∀ f : s,
        ((ModuleCat.derivedExtensionOfScalars
          (algebraMap R (Localization.Away f.1))).obj K).IsMPseudoCoherent m := sorry
-- Proof strategy: use `IsMPseudoCoherent.extension` in the forward direction and
-- `of_localizationSpan` in the reverse direction.

end CategoryTheory.DerivedCategory.IsMPseudoCoherent

namespace CategoryTheory.DerivedCategory.IsPseudoCoherent

variable {R : Type u} [CommRing R]

/-- Tag 066D: pseudo-coherence descends from a principal-open cover. -/
@[stacks 066D "pseudo-coherence on a principal-open cover"]
theorem of_localizationSpan (s : Set R) (hs : Ideal.span s = ⊤)
    {K : DerivedCategory (ModuleCat.{v, u} R)}
    (hK : ∀ f : s,
      ((ModuleCat.derivedExtensionOfScalars
        (algebraMap R (Localization.Away f.1))).obj K).IsPseudoCoherent) :
    K.IsPseudoCoherent := sorry
-- Proof strategy: rewrite pseudo-coherence as `m`-pseudo-coherence for every `m`, apply
-- `IsMPseudoCoherent.of_localizationSpan` degreewise, and reassemble the canonical
-- pseudo-coherent model.

/-- Tag 066D: pseudo-coherence is local on a principal-open cover. -/
@[stacks 066D "pseudo-coherence is principal-open local"]
theorem iff_localizationSpan (s : Set R) (hs : Ideal.span s = ⊤)
    (K : DerivedCategory (ModuleCat.{v, u} R)) :
    K.IsPseudoCoherent ↔
      ∀ f : s,
        ((ModuleCat.derivedExtensionOfScalars
          (algebraMap R (Localization.Away f.1))).obj K).IsPseudoCoherent := sorry
-- Proof strategy: use `IsPseudoCoherent.extension` in the forward direction and
-- `of_localizationSpan` in the reverse direction.

end CategoryTheory.DerivedCategory.IsPseudoCoherent
