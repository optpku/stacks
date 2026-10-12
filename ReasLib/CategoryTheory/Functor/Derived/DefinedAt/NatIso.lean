/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Filtered.EssentiallyConstant.Transport
public import ReasLib.CategoryTheory.Functor.Derived.DefinedAt.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Naturality of source-defined derived functors

Source-definedness is a property of the localization-indexed diagram, hence is invariant under
natural isomorphism of the source functor.  This file exposes both pointwise and everywhere
transport without registering bidirectional instances.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

variable {C : Type u₁} {D : Type u₂}
  [Category.{v₁} C] [Category.{v₂} D]

/-- Source-definedness of a pointwise right-derived value transports along a natural
isomorphism of source functors. -/
@[stacks 05S9 "right-derived source-definedness under natural isomorphism"]
theorem RightDerived.DefinedAt.of_natIso
    (S : MorphismProperty C) {F G : C ⥤ D} (X : C)
    [RightDerived.DefinedAt F S X] (e : F ≅ G) :
    RightDerived.DefinedAt G S X := sorry

/-- Source-definedness of a pointwise right-derived value is invariant under a natural
isomorphism of source functors. -/
@[stacks 05S9 "right-derived source-definedness iff under natural isomorphism"]
theorem RightDerived.DefinedAt.iff_of_natIso
    (S : MorphismProperty C) {F G : C ⥤ D} (X : C) (e : F ≅ G) :
    RightDerived.DefinedAt F S X ↔ RightDerived.DefinedAt G S X := sorry

/-- Everywhere source-definedness of a right-derived functor transports along a natural
isomorphism of source functors. -/
@[stacks 05S9 "everywhere right-derived definedness under natural isomorphism"]
theorem RightDerived.EverywhereDefined.of_iso
    (S : MorphismProperty C) {F G : C ⥤ D}
    [RightDerived.EverywhereDefined F S] (e : F ≅ G) :
    RightDerived.EverywhereDefined G S := sorry

/-- Everywhere source-definedness of a right-derived functor is invariant under a natural
isomorphism of source functors. -/
@[stacks 05S9 "everywhere right-derived definedness iff under natural isomorphism"]
theorem RightDerived.EverywhereDefined.iff_of_iso
    (S : MorphismProperty C) {F G : C ⥤ D} (e : F ≅ G) :
    RightDerived.EverywhereDefined F S ↔
      RightDerived.EverywhereDefined G S := sorry

/-- Source-definedness of a pointwise left-derived value transports along a natural
isomorphism of source functors. -/
@[stacks 05S9 "left-derived source-definedness under natural isomorphism"]
theorem LeftDerived.DefinedAt.of_natIso
    (S : MorphismProperty C) {F G : C ⥤ D} (X : C)
    [LeftDerived.DefinedAt F S X] (e : F ≅ G) :
    LeftDerived.DefinedAt G S X := sorry

/-- Source-definedness of a pointwise left-derived value is invariant under a natural
isomorphism of source functors. -/
@[stacks 05S9 "left-derived source-definedness iff under natural isomorphism"]
theorem LeftDerived.DefinedAt.iff_of_natIso
    (S : MorphismProperty C) {F G : C ⥤ D} (X : C) (e : F ≅ G) :
    LeftDerived.DefinedAt F S X ↔ LeftDerived.DefinedAt G S X := sorry

/-- Everywhere source-definedness of a left-derived functor transports along a natural
isomorphism of source functors. -/
@[stacks 05S9 "everywhere left-derived definedness under natural isomorphism"]
theorem LeftDerived.EverywhereDefined.of_iso
    (S : MorphismProperty C) {F G : C ⥤ D}
    [LeftDerived.EverywhereDefined F S] (e : F ≅ G) :
    LeftDerived.EverywhereDefined G S := sorry

/-- Everywhere source-definedness of a left-derived functor is invariant under a natural
isomorphism of source functors. -/
@[stacks 05S9 "everywhere left-derived definedness iff under natural isomorphism"]
theorem LeftDerived.EverywhereDefined.iff_of_iso
    (S : MorphismProperty C) {F G : C ⥤ D} (e : F ≅ G) :
    LeftDerived.EverywhereDefined F S ↔
      LeftDerived.EverywhereDefined G S := sorry

end CategoryTheory.Functor
