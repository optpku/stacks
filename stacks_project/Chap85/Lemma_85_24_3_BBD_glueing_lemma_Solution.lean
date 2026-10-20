/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Bounded
public import stacks_project.Chap85.Situation_85_24_1_LocallyGiven

/-!
# Compatible isomorphisms of solutions and uniform lower bounds

A solution isomorphism is compatible when its restrictions intertwine the given
identifications `ρ_U`. A locally given datum is uniformly bounded below when a
single integer bounds cohomology of every `E_U` from below.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open RingedSite RingedSite.Hom
open RingedSite.ModuleDerived

noncomputable section

universe u v w uB vB

namespace RingedSite.ModuleDerived

variable {X : RingedSite.{u, v, w}}
variable {B : Type uB} [Category.{vB} B]
variable [UnivLE.{max u v, w}]
variable {D : LocallyGiven.{u, v, w, w, uB, vB} X B}

namespace Solution

/-- An isomorphism of global objects is compatible with two solutions when its
restrictions intertwine the identifications `ρ_U`. -/
abbrev IsCompatibleIso (S S' : Solution D) (e : S.obj ≅ S'.obj) : Prop :=
  ∀ U : B,
    (localizedRestrictionDerived.{w} X (D.u.obj U)).map e.hom ≫ (S'.iso U).hom =
      (S.iso U).hom

/-- Equational form of compatibility of an isomorphism between solutions. -/
theorem IsCompatibleIso.w {S S' : Solution D} {e : S.obj ≅ S'.obj}
    (h : IsCompatibleIso S S' e) (U : B) :
    (localizedRestrictionDerived.{w} X (D.u.obj U)).map e.hom ≫ (S'.iso U).hom =
      (S.iso U).hom :=
  sorry

end Solution

namespace LocallyGiven

/-- A locally given datum is uniformly bounded below when there is a single
integer `t` such that `(DerivedCategory.homologyFunctor _ i).obj (D.obj U)` is
zero for all `U : B` and all `i < t`. -/
def uniformlyBoundedBelow (D : LocallyGiven.{u, v, w, w, uB, vB} X B) : Prop :=
  ∃ t : ℤ, ∀ (U : B) (i : ℤ), i < t →
    IsZero ((DerivedCategory.homologyFunctor _ i).obj (D.obj U))

/-- Unfolding of uniform boundedness below. -/
theorem uniformlyBoundedBelow_iff (D : LocallyGiven.{u, v, w, w, uB, vB} X B) :
    uniformlyBoundedBelow D ↔
      ∃ t : ℤ, ∀ (U : B) (i : ℤ), i < t →
        IsZero ((DerivedCategory.homologyFunctor _ i).obj (D.obj U)) :=
  sorry

end LocallyGiven

end RingedSite.ModuleDerived
