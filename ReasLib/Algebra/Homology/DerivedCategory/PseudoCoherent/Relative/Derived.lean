/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.Relative.Presentation
import Mathlib.Tactic.CrossRefAttribute

/-!
# Relative pseudo-coherence in derived categories

This leaf puts the presentationwise predicate directly on derived objects and
packages the exact restriction-of-scalars functor used in its definition.
@stack 065I
-/

@[expose] public section

noncomputable section

open CategoryTheory
open ComplexShape

universe u v

namespace CategoryTheory.ModuleCat

/-- The derived functor induced by restriction of scalars along a commutative ring homomorphism. -/
@[stacks 0BYX "derived restriction of scalars for relative pseudo-coherence"]
noncomputable abbrev restrictScalarsMapDerivedCategory
    {R : Type u} {A : Type v} [CommRing R] [CommRing A] (f : R →+* A) :=
  (ModuleCat.restrictScalars f).mapDerivedCategory

end CategoryTheory.ModuleCat

namespace CategoryTheory.DerivedCategory

/-- Restrict a derived `A`-complex along a polynomial presentation of `A` over `R`. -/
@[stacks 065I "polynomial presentation restriction in the derived category"]
abbrev polynomialPresentationRestriction
    {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Algebra R A]
    {n : ℕ} (α : MvPolynomial (Fin n) R →ₐ[R] A)
    (K : DerivedCategory (ModuleCat A)) :
    DerivedCategory (ModuleCat (MvPolynomial (Fin n) R)) :=
  (ModuleCat.restrictScalarsMapDerivedCategory α.toRingHom).obj K

/-- A derived `A`-complex is `m`-pseudo-coherent relative to `R` when every surjective finite
polynomial presentation of `A` over `R` makes its restriction absolutely `m`-pseudo-coherent. -/
@[stacks 065I "derived relative m-pseudo-coherence"]
abbrev IsMPseudoCoherentRelativeTo
    (R : Type u) [CommRing R] {A : Type v} [CommRing A] [Algebra R A]
    [Algebra.FiniteType R A] (K : DerivedCategory (ModuleCat A)) (m : ℤ) : Prop :=
  ∀ (n : ℕ) (α : MvPolynomial (Fin n) R →ₐ[R] A), Function.Surjective α →
    (K.polynomialPresentationRestriction α).IsMPseudoCoherent m

/-- A derived `A`-complex is pseudo-coherent relative to `R` when it is `m`-pseudo-coherent
relative to `R` for every integer `m`. -/
@[stacks 065I "derived relative pseudo-coherence"]
abbrev IsPseudoCoherentRelativeTo
    (R : Type u) [CommRing R] {A : Type v} [CommRing A] [Algebra R A]
    [Algebra.FiniteType R A] (K : DerivedCategory (ModuleCat A)) : Prop :=
  ∀ m : ℤ, K.IsMPseudoCoherentRelativeTo R m

/-- Relative `m`-pseudo-coherence of a derived complex can be checked on one surjective finite
polynomial presentation of its finite type algebra. -/
@[stacks 065I "derived relative m-pseudo-coherence over some presentation"]
theorem isMPseudoCoherentRelativeTo_iff_overSomePolynomialPresentation
    {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.FiniteType R A] (K : DerivedCategory (ModuleCat A)) (m : ℤ) :
    K.IsMPseudoCoherentRelativeTo R m ↔
      ∃ (n : ℕ) (α : MvPolynomial (Fin n) R →ₐ[R] A), Function.Surjective α ∧
        (K.polynomialPresentationRestriction α).IsMPseudoCoherent m := sorry

end CategoryTheory.DerivedCategory
