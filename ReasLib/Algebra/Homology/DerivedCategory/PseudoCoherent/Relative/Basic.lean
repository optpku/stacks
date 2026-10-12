/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.MvPolynomial.Basic
public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent
import Mathlib.Tactic.CrossRefAttribute

/-!
# Relative pseudo-coherence

@stack 065I

This file owns presentationwise relative pseudo-coherence for complexes and
modules over a finite type algebra.  Absolute pseudo-coherence remains owned
by `ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent`.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open ComplexShape

universe u v w

namespace CategoryTheory

namespace CochainComplex

/-- Restrict a cochain complex of `A`-modules along a polynomial presentation of `A` over `R`. -/
@[stacks 065I "polynomial presentation restriction for complexes"]
abbrev polynomialPresentationRestriction
    {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Algebra R A]
    (K : CochainComplex (ModuleCat A) ℤ) {n : ℕ}
    (α : MvPolynomial (Fin n) R →ₐ[R] A) :
    CochainComplex (ModuleCat (MvPolynomial (Fin n) R)) ℤ :=
  ((ModuleCat.restrictScalars α.toRingHom).mapHomologicalComplex (up ℤ)).obj K

/-- A cochain complex of `A`-modules is `m`-pseudo-coherent relative to `R` when every surjective
finite polynomial presentation of `A` over `R` makes its restriction absolutely
`m`-pseudo-coherent. -/
@[stacks 065I "(1), relative m-pseudo-coherent complex"]
abbrev IsMPseudoCoherentRelativeTo
    (R : Type u) [CommRing R] {A : Type v} [CommRing A] [Algebra R A]
    [Algebra.FiniteType R A]
    (K : CochainComplex (ModuleCat A) ℤ) (m : ℤ) : Prop :=
  ∀ (n : ℕ) (α : MvPolynomial (Fin n) R →ₐ[R] A) (_ : Function.Surjective α),
    (K.polynomialPresentationRestriction α).IsMPseudoCoherent m

/-- A cochain complex of `A`-modules is pseudo-coherent relative to `R` when it is
`m`-pseudo-coherent relative to `R` for every integer `m`. -/
@[stacks 065I "(2), relative pseudo-coherent complex"]
abbrev IsPseudoCoherentRelativeTo
    (R : Type u) [CommRing R] {A : Type v} [CommRing A] [Algebra R A]
    [Algebra.FiniteType R A]
    (K : CochainComplex (ModuleCat A) ℤ) : Prop :=
  ∀ m : ℤ, K.IsMPseudoCoherentRelativeTo R m

end CochainComplex

namespace ModuleCat

/-- An `A`-module is `m`-pseudo-coherent relative to `R` when its degree-zero complex is
`m`-pseudo-coherent relative to `R`. -/
@[stacks 065I "(3), relative m-pseudo-coherent module"]
abbrev IsMPseudoCoherentRelativeTo
    (R : Type u) [CommRing R] {A : Type v} [CommRing A] [Algebra R A]
    [Algebra.FiniteType R A]
    (M : ModuleCat A) (m : ℤ) : Prop :=
  ((CochainComplex.singleFunctor (ModuleCat A) (0 : ℤ)).obj M).IsMPseudoCoherentRelativeTo R m

/-- An `A`-module is pseudo-coherent relative to `R` when its degree-zero complex is
pseudo-coherent relative to `R`. -/
@[stacks 065I "(4), relative pseudo-coherent module"]
abbrev IsPseudoCoherentRelativeTo
    (R : Type u) [CommRing R] {A : Type v} [CommRing A] [Algebra R A]
    [Algebra.FiniteType R A]
    (M : ModuleCat A) : Prop :=
  ((CochainComplex.singleFunctor (ModuleCat A) (0 : ℤ)).obj M).IsPseudoCoherentRelativeTo R

end ModuleCat

namespace Module

/-- An ordinary `A`-module is `m`-pseudo-coherent relative to `R` through its canonical bundled
module object. -/
@[stacks 065I "ordinary-module relative m-pseudo-coherence"]
abbrev IsMPseudoCoherentRelativeTo
    (R : Type u) [CommRing R] (A : Type v) [CommRing A] [Algebra R A]
    [Algebra.FiniteType R A]
    (M : Type w) [AddCommGroup M] [Module A M] (m : ℤ) : Prop :=
  (ModuleCat.of A M).IsMPseudoCoherentRelativeTo R m

/-- An ordinary `A`-module is pseudo-coherent relative to `R` through its canonical bundled
module object. -/
@[stacks 065I "ordinary-module relative pseudo-coherence"]
abbrev IsPseudoCoherentRelativeTo
    (R : Type u) [CommRing R] (A : Type v) [CommRing A] [Algebra R A]
    [Algebra.FiniteType R A]
    (M : Type w) [AddCommGroup M] [Module A M] : Prop :=
  (ModuleCat.of A M).IsPseudoCoherentRelativeTo R

end Module

end CategoryTheory
