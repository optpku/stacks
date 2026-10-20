/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Size
public import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
# Uniform cardinal bounds on finite-type fields

A presheaf on schemes over a base is bounded on finite-type fields if its
values on their spectra have cardinalities bounded by the size of a single
scheme over the base.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Over

/-- The values of `F` on spectra of finite-type fields over `S` have
cardinalities bounded by the size of some scheme over `S`. -/
def boundedOnFiniteTypeFields {S : Scheme.{u}} (F : (Over S)ᵒᵖ ⥤ Type u) :
    Prop :=
  ∃ U : Over S, ∀ (k : Type u) [Field k] (f : Spec (CommRingCat.of k) ⟶ S)
    [LocallyOfFiniteType f],
      Cardinal.mk (F.obj (op (Over.mk f))) ≤ U.left.size

/-- Boundedness on finite-type fields is equivalent to a uniform comparison
of their value cardinalities with the size of a scheme over the base. -/
theorem boundedOnFiniteTypeFields_iff {S : Scheme.{u}}
    (F : (Over S)ᵒᵖ ⥤ Type u) :
    boundedOnFiniteTypeFields F ↔
      ∃ U : Over S, ∀ (k : Type u) [Field k]
        (f : Spec (CommRingCat.of k) ⟶ S) [LocallyOfFiniteType f],
          Cardinal.mk (F.obj (op (Over.mk f))) ≤ U.left.size :=
  sorry

end AlgebraicGeometry.Scheme.Over
