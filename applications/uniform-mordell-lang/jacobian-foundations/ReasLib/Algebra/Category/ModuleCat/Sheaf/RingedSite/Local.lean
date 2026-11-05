module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
public import Mathlib.CategoryTheory.Sites.CoversTop.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Cover-local object properties for module sheaves

This file turns a family of object properties on slice sites into one object property on the
original site. It is the neutral combinator behind local freeness, local presentations, and
other cover-local conditions.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {R : Sheaf J RingCat.{w}}

/-- The cover-localization of a family of object properties on the slice module categories. -/
def locally
    (P : (U : C) → ObjectProperty (SheafOfModules.{w} (R.over U))) :
    ObjectProperty (SheafOfModules.{w} R) :=
  fun M ↦ ∃ (I : Type u) (U : I → C), J.CoversTop U ∧
    ∀ i : I, P (U i) (M.over (U i))

/-- The defining cover criterion for `locally P`. -/
@[stacks 03DN "cover-local object property"]
theorem locally_iff
    (P : (U : C) → ObjectProperty (SheafOfModules.{w} (R.over U)))
    (M : SheafOfModules.{w} R) :
    locally P M ↔
      ∃ (I : Type u) (U : I → C), J.CoversTop U ∧
        ∀ i : I, P (U i) (M.over (U i)) := sorry

/-- A property holding on every member of a cover gives the corresponding cover-local
property. -/
theorem locally_of_cover
    (P : (U : C) → ObjectProperty (SheafOfModules.{w} (R.over U)))
    (M : SheafOfModules.{w} R) {I : Type u} (U : I → C)
    (hU : J.CoversTop U) (hM : ∀ i : I, P (U i) (M.over (U i))) :
    locally P M := sorry

/-- Cover-localization is monotone in the local object property. -/
theorem locally_mono
    {P Q : (U : C) → ObjectProperty (SheafOfModules.{w} (R.over U))}
    (h : ∀ U : C, P U ≤ Q U) :
    locally P ≤ locally Q := sorry

/-- Cover-localization preserves invariance under isomorphism. -/
instance locally_isClosedUnderIsomorphisms
    (P : (U : C) → ObjectProperty (SheafOfModules.{w} (R.over U)))
    [∀ U : C, (P U).IsClosedUnderIsomorphisms] :
    (locally P).IsClosedUnderIsomorphisms := sorry

end SheafOfModules.RingedSite
