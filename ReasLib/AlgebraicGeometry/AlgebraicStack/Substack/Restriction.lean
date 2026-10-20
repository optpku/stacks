/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Substack.Points
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Basic
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Equivalence.Basic

/-!
# Restriction of closed substacks

A closed substack restricts to the whole source of a morphism when the
canonical projection of its two-fibre product is an equivalence over the base.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.Substack

/-- A closed substack restricts to the whole source of a morphism when the
second projection of its two-fibre product is an equivalence over the base. -/
def restrictsTo {S : Scheme.{u}} {X U : GroupoidsOver S}
    (P : ObjectProperty X.total) (hP : IsClosed X P) (j : U ⟶ X) : Prop :=
  (FiberedCategoryOver.Groupoids.toBasedFunctor
    (TwoFibreProduct.snd.{u + 1, u, u + 1, u} (closedInclusion X P hP) j)).IsEquivalence

/-- Restricting a closed substack to the whole source is equivalent to the
canonical two-fibre-product projection being an equivalence over the base. -/
theorem restrictsTo_iff {S : Scheme.{u}} {X U : GroupoidsOver S}
    (P : ObjectProperty X.total) (hP : IsClosed X P) (j : U ⟶ X) :
    restrictsTo P hP j ↔
      (FiberedCategoryOver.Groupoids.toBasedFunctor
        (TwoFibreProduct.snd.{u + 1, u, u + 1, u}
          (closedInclusion X P hP) j)).IsEquivalence :=
  Iff.rfl

end AlgebraicGeometry.AlgebraicStack.Substack
