module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Perfect
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Localization
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Local models for perfect derived module sheaves

Perfectness can be tested after covering every object by restrictions admitting strictly perfect
models.  The terminal-object criterion from Lemma 21.47.2 is a source-facing consequence of this
local API.
-/

open CategoryTheory CategoryTheory.Limits ComplexShape
open RingedSite (ModuleCat)
open RingedSite.CochainComplex (IsStrictlyPerfect)
open RingedSite.Hom (ModuleDerived localizedRestriction localizedRestrictionDerived)

noncomputable section

universe u v w

set_option checkBinderAnnotations false

namespace RingedSite.DerivedCategory

variable {X : RingedSite.{u, v, w}} [UnivLE.{max u v, w}]
variable [∀ U : X, HasWeakSheafify (X.localization U).siteTopology AddCommGrpCat.{w}]
variable [∀ U : X,
  (X.localization U).siteTopology.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [∀ U : X, PreservesFiniteLimits (localizedRestriction.{w} X U)]
variable [∀ U : X, PreservesFiniteColimits (localizedRestriction.{w} X U)]

/-- A derived module sheaf has a strictly perfect model over `U` if its restriction to `X/U`
is isomorphic to the localization of a strictly perfect complex. -/
@[stacks 08G6 "local strictly-perfect model"]
def HasStrictlyPerfectModel
    (K : ModuleDerived.{w} X) (U : X) : Prop :=
  ∃ E : CochainComplex (ModuleCat.{w} (X.localization U)) ℤ,
    IsStrictlyPerfect E ∧
      ∃ α : DerivedCategory.Q.obj E ⟶ (localizedRestrictionDerived.{w} X U).obj K,
        IsIso α

/-- Perfectness is equivalent to locally admitting strictly perfect models on a cover of every
object. -/
@[stacks 08G6 "local criterion"]
theorem isPerfect_iff_locally_hasStrictlyPerfectModel
    (K : ModuleDerived.{w} X) :
    K.IsPerfect ↔
      ∀ U : X, ∃ T : X.siteTopology.Cover U, ∀ I : T.Arrow,
        HasStrictlyPerfectModel K I.Y := sorry

/-- Lemma 21.47.2 (1): strictly perfect models on a cover of a terminal object imply
perfectness. -/
@[stacks 08G6 "(1)"]
theorem isPerfect_of_cover_of_isTerminal
    (K : ModuleDerived.{w} X) (U : X) (hU : IsTerminal U)
    (hcover : ∃ T : X.siteTopology.Cover U, ∀ I : T.Arrow,
      HasStrictlyPerfectModel K I.Y) :
    K.IsPerfect := sorry

end RingedSite.DerivedCategory
