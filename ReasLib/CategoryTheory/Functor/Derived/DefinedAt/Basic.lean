/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Filtered.EssentiallyConstant.Limits

/-!
# Derived functors defined at an object

This file owns the model-independent source notion that a derived functor is defined at an
object. The defining condition retains an essentially constant presentation of the relevant
localization-indexed diagram, so it is stronger than Mathlib's pointwise Kan-extension existence
predicate. The canonical bridge instances forget this extra presentation data.
-/

@[expose] public section

open CategoryTheory Limits MorphismProperty

noncomputable section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

variable {D : Type u₁} {D' : Type u₂}
  [Category.{v₁} D] [Category.{v₂} D']

/-- the left derived functor of `F` is source-defined at `X` when the pro-diagram
indexed by `S / X` is essentially constant. -/
@[stacks 05S9]
class LeftDerived.DefinedAt (F : D ⥤ D') (S : MorphismProperty D) (X : D) : Prop where
  /-- The localization-indexed pro-diagram computing the left-derived value at `X` is
  essentially constant. -/
  isEssentiallyConstant :
    IsCofiltered.IsEssentiallyConstant (StructuredArrow.proj (S.Q.obj X) S.Q ⋙ F)

/-- the right derived functor of `F` is source-defined at `X` when the ind-diagram
indexed by `X / S` is essentially constant. -/
@[stacks 05S9]
class RightDerived.DefinedAt (F : D ⥤ D') (S : MorphismProperty D) (X : D) : Prop where
  /-- The localization-indexed ind-diagram computing the right-derived value at `X` is
  essentially constant. -/
  isEssentiallyConstant :
    IsFiltered.IsEssentiallyConstant (CostructuredArrow.proj S.Q (S.Q.obj X) ⋙ F)

namespace RightDerived

/-- The right derived functor of `F` is defined everywhere when its localization-indexed
ind-diagram is essentially constant at every object. -/
@[stacks 05SV "everywhere-defined right derived functor"]
class EverywhereDefined (F : D ⥤ D') (S : MorphismProperty D) : Prop where
  /-- Source-definedness at each object. -/
  definedAt : ∀ X : D, RightDerived.DefinedAt F S X

end RightDerived

namespace LeftDerived

/-- The left derived functor of `F` is defined everywhere when its localization-indexed
pro-diagram is essentially constant at every object. -/
@[stacks 05SV "everywhere-defined left derived functor"]
class EverywhereDefined (F : D ⥤ D') (S : MorphismProperty D) : Prop where
  /-- Source-definedness at each object. -/
  definedAt : ∀ X : D, LeftDerived.DefinedAt F S X

end LeftDerived

/-- An everywhere-defined right derived functor supplies source-definedness at every object to
typeclass search. -/
@[stacks 05S9 "everywhere-defined right derived functor at an object"]
instance RightDerived.EverywhereDefined.toDefinedAt
    {F : D ⥤ D'} {S : MorphismProperty D} {X : D}
    [RightDerived.EverywhereDefined F S] :
    RightDerived.DefinedAt F S X := RightDerived.EverywhereDefined.definedAt X

/-- An everywhere-defined left derived functor supplies source-definedness at every object to
typeclass search. -/
@[stacks 05S9 "everywhere-defined left derived functor at an object"]
instance LeftDerived.EverywhereDefined.toDefinedAt
    {F : D ⥤ D'} {S : MorphismProperty D} {X : D}
    [LeftDerived.EverywhereDefined F S] :
    LeftDerived.DefinedAt F S X := LeftDerived.EverywhereDefined.definedAt X

/-- An everywhere-defined right derived functor is equivalently source-defined at every
object. -/
@[stacks 05S9 "everywhere-defined right derived functor criterion"]
theorem RightDerived.EverywhereDefined.iff (F : D ⥤ D') (S : MorphismProperty D) :
    RightDerived.EverywhereDefined F S ↔
      ∀ X : D, RightDerived.DefinedAt F S X := sorry

/-- An everywhere-defined left derived functor is equivalently source-defined at every
object. -/
@[stacks 05S9 "everywhere-defined left derived functor criterion"]
theorem LeftDerived.EverywhereDefined.iff (F : D ⥤ D') (S : MorphismProperty D) :
    LeftDerived.EverywhereDefined F S ↔
      ∀ X : D, LeftDerived.DefinedAt F S X := sorry

/-- Forgetting the essentially constant presentation of a source-defined right-derived value
yields Mathlib's pointwise right-derived existence property. The converse is not asserted. -/
@[stacks 05S9 "source-defined right-derived value implies pointwise existence"]
noncomputable instance RightDerived.DefinedAt.hasPointwise
    {F : D ⥤ D'} {S : MorphismProperty D} {X : D}
    [RightDerived.DefinedAt F S X] :
    F.HasPointwiseRightDerivedFunctorAt S X :=
  ⟨⟨⟨(RightDerived.DefinedAt.isEssentiallyConstant (F := F) (S := S) (X := X)).colimitCocone⟩⟩⟩

/-- A right-derived functor defined at every source object supplies Mathlib's global pointwise
existence owner. -/
@[stacks 05S9 "everywhere-defined right-derived functor implies pointwise existence"]
noncomputable instance RightDerived.EverywhereDefined.hasPointwise
    {F : D ⥤ D'} {S : MorphismProperty D}
    [RightDerived.EverywhereDefined F S] :
    F.HasPointwiseRightDerivedFunctor S :=
  fun X ↦ @RightDerived.DefinedAt.hasPointwise _ _ _ _ F S X
    (RightDerived.EverywhereDefined.definedAt X)

/-- Forgetting the essentially constant presentation of a source-defined left-derived value
yields Mathlib's pointwise left-derived existence property. The converse is not asserted. -/
@[stacks 05S9 "source-defined left-derived value implies pointwise existence"]
noncomputable instance LeftDerived.DefinedAt.hasPointwise
    {F : D ⥤ D'} {S : MorphismProperty D} {X : D}
    [LeftDerived.DefinedAt F S X] :
    F.HasPointwiseLeftDerivedFunctorAt S X :=
  ⟨⟨⟨(LeftDerived.DefinedAt.isEssentiallyConstant (F := F) (S := S) (X := X)).limitCone⟩⟩⟩

/-- A left-derived functor defined at every source object supplies Mathlib's global pointwise
existence owner. -/
@[stacks 05S9 "everywhere-defined left-derived functor implies pointwise existence"]
noncomputable instance LeftDerived.EverywhereDefined.hasPointwise
    {F : D ⥤ D'} {S : MorphismProperty D}
    [LeftDerived.EverywhereDefined F S] :
    F.HasPointwiseLeftDerivedFunctor S :=
  fun X ↦ @LeftDerived.DefinedAt.hasPointwise _ _ _ _ F S X
    (LeftDerived.EverywhereDefined.definedAt X)


end CategoryTheory.Functor
