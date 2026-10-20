/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Functor.Derived.DefinedAt.Basic
public import ReasLib.CategoryTheory.Functor.Derived.PointwiseValue
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Computing Pointwise Derived Functors

This leaf records the objectwise condition that a source-defined derived value is already computed
by the original functor.  In the Stacks sense, computation includes essential constancy of the
localization-indexed diagram, not merely existence of its pointwise Kan extension.  The canonical
bridge from `Functor.RightDerived.DefinedAt` or `Functor.LeftDerived.DefinedAt` supplies Mathlib's weaker pointwise
existence API automatically.

The definitions use an arbitrary localization class and do not depend on a particular
derived-category model.
-/

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.Functor

variable {D : Type u₁} {D' : Type u₂}
  [Category.{v₁} D] [Category.{v₂} D']
  (F : D ⥤ D') (S : MorphismProperty D) (X : D)
  [S.ContainsIdentities]

/-- Stacks 05SX: `X` computes the right-derived value of `F` when its localization-indexed
diagram is essentially constant and its identity-denominator leg is an isomorphism. -/
@[stacks 05SX]
class RightDerived.ComputesAt : Prop extends RightDerived.DefinedAt F S X where
  /-- The canonical identity-denominator leg is invertible. -/
  isIso_valueLeg :
    IsIso (CategoryTheory.Functor.RightDerived.Value.ι F S (𝟙 X) (S.id_mem X))

attribute [instance] RightDerived.ComputesAt.toDefinedAt
attribute [instance] RightDerived.ComputesAt.isIso_valueLeg

/-- Stacks 05SX: the object property of points which compute the pointwise right-derived value
of `F`. -/
@[stacks 05SX]
abbrev RightDerived.ComputesAt.objects : ObjectProperty D :=
  fun X ↦ RightDerived.ComputesAt F S X

/-- Stacks 05SX: `X` computes the left-derived value of `F` when its localization-indexed
diagram is essentially constant and its identity-denominator projection is an isomorphism. -/
@[stacks 05SX]
class LeftDerived.ComputesAt : Prop extends LeftDerived.DefinedAt F S X where
  /-- The canonical identity-denominator projection is invertible. -/
  isIso_valueProjection :
    IsIso (CategoryTheory.Functor.LeftDerived.Value.π F S (𝟙 X) (S.id_mem X))

attribute [instance] LeftDerived.ComputesAt.toDefinedAt
attribute [instance] LeftDerived.ComputesAt.isIso_valueProjection

/-- Stacks 05SX: the object property of points which compute the pointwise left-derived value
of `F`. -/
@[stacks 05SX]
abbrev LeftDerived.ComputesAt.objects : ObjectProperty D :=
  fun X ↦ LeftDerived.ComputesAt F S X

section Right

variable [Functor.RightDerived.EverywhereDefined F S]

/-- Stacks 05SX: when the right-derived functor is source-defined everywhere, computation at `X`
is equivalent to invertibility of the total right-derived unit at `X`. -/
@[stacks 05SX]
theorem RightDerived.ComputesAt.iff :
    RightDerived.ComputesAt F S X ↔
      IsIso ((F.totalRightDerivedUnit S.Q S).app X) := sorry

/-- Stacks 05SX: the computation criterion is independent of the chosen localization model.
For any localization `Q` at `S`, computation at `X` is equivalent to invertibility of the
corresponding total right-derived unit. -/
@[stacks 05SX]
theorem RightDerived.ComputesAt.iff_of_isLocalization
    {E : Type u₃} [Category.{v₃} E] (Q : D ⥤ E) [Q.IsLocalization S] :
    RightDerived.ComputesAt F S X ↔
      IsIso ((F.totalRightDerivedUnit Q S).app X) := sorry

end Right

section Left

variable [Functor.LeftDerived.EverywhereDefined F S]

/-- Stacks 05SX: when the left-derived functor is source-defined everywhere, computation at `X`
is equivalent to invertibility of the total left-derived counit at `X`. -/
@[stacks 05SX]
theorem LeftDerived.ComputesAt.iff :
    LeftDerived.ComputesAt F S X ↔
      IsIso ((F.totalLeftDerivedCounit S.Q S).app X) := sorry

/-- Stacks 05SX: the left-derived computation criterion is independent of the chosen
localization model. For any localization `Q` at `S`, computation at `X` is equivalent to
invertibility of the corresponding total left-derived counit. -/
@[stacks 05SX]
theorem LeftDerived.ComputesAt.iff_of_isLocalization
    {E : Type u₃} [Category.{v₃} E] (Q : D ⥤ E) [Q.IsLocalization S] :
    LeftDerived.ComputesAt F S X ↔
      IsIso ((F.totalLeftDerivedCounit Q S).app X) := sorry

end Left


end CategoryTheory.Functor
