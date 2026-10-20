module

public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.Flat.Availability
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Pseudo-coherence under derived extension of scalars

@stack 0650
@stack 0H76

This file states scalar-extension results using an explicit ring homomorphism.  The API is owned
by the pseudo-coherence predicates, so it is independent of `Algebra` instances and tensor
notation chosen by a downstream application. The existing derived-availability witness is
explicit at its first use; in a module universe containing the base ring, the canonical
cell-model producer supplies it.
-/

open CategoryTheory

noncomputable section

universe uR uS v

namespace CategoryTheory.DerivedCategory.IsMPseudoCoherent

variable {R : Type uR} {S : Type uS} [CommRing R] [CommRing S]

/-- Lemma 15.65.12 (1) (0650): derived extension of scalars preserves
`m`-pseudo-coherence. -/
@[stacks 0650 "derived extension preserves m-pseudo-coherence"]
theorem extension {K : DerivedCategory (ModuleCat.{v, uR} R)} {m : ℤ}
    (hK : K.IsMPseudoCoherent m) (σ : R →+* S)
    [hasLeftDerived : (ModuleCat.extendScalarsToDerived.{uR, uS, v} σ).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso (ModuleCat.{v, uR} R) (ComplexShape.up ℤ))] :
    ((ModuleCat.derivedExtensionOfScalars.{uR, uS, v} σ).obj K).IsMPseudoCoherent m := sorry
-- Proof strategy: extend a bounded-above finite-free approximation of `K` termwise along `σ`,
-- identify the resulting complex with derived extension, and transport the required homology
-- isomorphisms and degree-`m` epimorphism through the exact derived functor.

end CategoryTheory.DerivedCategory.IsMPseudoCoherent

namespace CategoryTheory.DerivedCategory.IsPseudoCoherent

variable {R : Type uR} {S : Type uS} [CommRing R] [CommRing S]

/-- Lemma 15.65.12 (2) (0650): derived extension of scalars preserves pseudo-coherence. -/
@[stacks 0650 "derived extension preserves pseudo-coherence"]
theorem extension {K : DerivedCategory (ModuleCat.{v, uR} R)}
    (hK : K.IsPseudoCoherent) (σ : R →+* S)
    [hasLeftDerived : (ModuleCat.extendScalarsToDerived.{uR, uS, v} σ).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso (ModuleCat.{v, uR} R) (ComplexShape.up ℤ))] :
    ((ModuleCat.derivedExtensionOfScalars.{uR, uS, v} σ).obj K).IsPseudoCoherent := sorry
-- Proof strategy: apply the `m`-pseudo-coherent extension theorem in every degree and use the
-- canonical all-degree characterization of pseudo-coherence.

/-- Lemma 15.76.4 (0H76): pseudo-coherence is reflected by derived extension along a surjection
with nilpotent kernel. -/
@[stacks 0H76 "pseudo-coherence across a nilpotent thickening"]
theorem extension_iff (σ : R →+* S)
    [hasLeftDerived : (ModuleCat.extendScalarsToDerived.{uR, uS, v} σ).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso (ModuleCat.{v, uR} R) (ComplexShape.up ℤ))]
    (hσ : Function.Surjective σ)
    (hker : IsNilpotent (RingHom.ker σ))
    (K : DerivedCategory (ModuleCat.{v, uR} R)) :
    ((ModuleCat.derivedExtensionOfScalars.{uR, uS, v} σ).obj K).IsPseudoCoherent ↔
      K.IsPseudoCoherent := sorry
-- Proof strategy: the reverse implication is `extension`; for reflection, use nilpotent
-- devissage along the surjection and lift finite free approximations through successive
-- square-zero quotients of `RingHom.ker σ`.

end CategoryTheory.DerivedCategory.IsPseudoCoherent
