/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.CompleteIntersection.RelativeGlobal.Basic
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Stability of Relative Global Complete Intersections

This module records the functorial operations on relative global complete
intersection presentations and algebras.

@stack 00SS
-/

open scoped TensorProduct

universe u v w

namespace Algebra

namespace Presentation

section

variable {R : Type u} {R' : Type v} {S : Type w}
variable [CommRing R] [CommRing R'] [CommRing S]
variable [Algebra R S] [Algebra R R']

/-- Relative global complete intersection presentations are preserved by
arbitrary base change. -/
theorem IsRelativeGlobalCompleteIntersection.baseChange
    {n c : ℕ} {P : Algebra.Presentation R S (Fin n) (Fin c)}
    (hP : P.IsRelativeGlobalCompleteIntersection) :
    (P.baseChange R').IsRelativeGlobalCompleteIntersection := sorry

/-- Passing from a finite presentation to its explicit quotient presentation
preserves the relative-global-complete-intersection condition. -/
theorem IsRelativeGlobalCompleteIntersection.naive
    {A : Type*} [CommRing A] [Algebra R A]
    {n c : ℕ} (P : Algebra.Presentation R A (Fin n) (Fin c))
    (hP : P.IsRelativeGlobalCompleteIntersection) :
    (Algebra.Presentation.naive :
      Algebra.Presentation R
        (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range P.relation))
        (Fin n) (Fin c)).IsRelativeGlobalCompleteIntersection := sorry

end

end Presentation

namespace IsRelativeGlobalCompleteIntersection

section

variable {R : Type u} {A : Type v} {B : Type w}
variable [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra R B]

/-- An equivalence of `R`-algebras transports the relative global complete
intersection property to the equivalent target. -/
theorem of_algEquiv (hA : IsRelativeGlobalCompleteIntersection R A) (e : A ≃ₐ[R] B) :
    IsRelativeGlobalCompleteIntersection R B := sorry

end

section

variable {R : Type u} {R' : Type v} {S : Type w}
variable [CommRing R] [CommRing R'] [CommRing S]
variable [Algebra R S] [Algebra R R']

/-- Relative global complete intersections are stable under arbitrary base change. -/
@[stacks 00SS]
theorem baseChange (hS : IsRelativeGlobalCompleteIntersection R S) :
    IsRelativeGlobalCompleteIntersection R' (R' ⊗[R] S) := sorry

/-- Localizing away from an element of a relative global complete intersection
again yields a relative global complete intersection. -/
@[stacks 00SS]
theorem localizationAway (hS : IsRelativeGlobalCompleteIntersection R S) (g : S) :
    IsRelativeGlobalCompleteIntersection R (Localization.Away g) := sorry

end

section

variable {R : Type u} {Rf : Type v} {S : Type w}
variable [CommRing R] [CommRing Rf] [CommRing S]
variable [Algebra R S] [Algebra R Rf] [Algebra Rf S] [IsScalarTower R Rf S]

/-- When `R → S` factors through a localization away from `f`, a relative global
complete intersection over `R` is one over that localization. -/
@[stacks 00SS]
theorem of_isLocalizationAway (f : R) [IsLocalization.Away f Rf]
    (hS : IsRelativeGlobalCompleteIntersection R S) :
    IsRelativeGlobalCompleteIntersection Rf S := sorry

end

end IsRelativeGlobalCompleteIntersection

end Algebra
