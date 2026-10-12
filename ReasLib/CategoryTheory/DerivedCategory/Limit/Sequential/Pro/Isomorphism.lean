/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Limit.Sequential.Pro
public import ReasLib.CategoryTheory.Pro.Sequential.Isomorphism

@[expose] public section

/-!
# Representative Criterion for Derived Stagewise Pro-Isomorphisms

This leaf connects the abstract invertibility predicate to concrete monotone
representatives and common refinements.
@stack 091B
-/

open CategoryTheory

noncomputable section

universe wA wSys u v

namespace CategoryTheory.DerivedLimit.Pro.isomorphisms

variable {A : Type u} [Category.{v} A] [Abelian A]
variable [HasDerivedCategory.{wA} A]
variable [HasDerivedCategory.{wSys} (SequentialInverseSystem A)]

/-- A derived morphism is a stagewise pro-isomorphism exactly when its
canonical sequential representative admits a representative inverse. -/
@[stacks 091B]
theorem iff_hasRepresentativeInverse
    {K L : DerivedCategory (SequentialInverseSystem A)} (f : K ⟶ L) :
    DerivedLimit.Pro.isomorphisms A f ↔
      (DerivedLimit.Pro.representative f).HasRepresentativeInverse := sorry

end CategoryTheory.DerivedLimit.Pro.isomorphisms
