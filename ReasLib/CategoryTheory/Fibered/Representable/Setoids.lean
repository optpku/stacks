/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.Tactic.CrossRefAttribute
-- Import decisions:
-- * `RepresentedBy` is public because `Functor.IsRepresentable` occurs in the criterion.
-- * `Representable` is public because it owns
--   `FiberedCategoryOver.Groupoids.IsRepresentable`.
-- * `Fibered.FiberIsoClassPresheaf.Basic` is public because it owns the canonical
--   `Functor.fiberIsoClassPresheaf`.
-- * `Fibered.InSetoids` is public because the criterion exposes
--   `Functor.IsFibered.InSetoids`.
public import Mathlib.CategoryTheory.RepresentedBy
public import ReasLib.CategoryTheory.Fibered.InSetoids
public import ReasLib.CategoryTheory.Fibered.Representable.Lifted
public import ReasLib.CategoryTheory.Fibered.FiberIsoClassPresheaf.Basic

/-!
# Representability through fiberwise isomorphism classes

The representability criterion for a category fibred in groupoids is expressed using the
canonical set-valued presheaf of fiberwise isomorphism classes.  Fine-grained projections and a
constructor keep applications from repeatedly unpacking the conjunction in the criterion.
-/

@[expose] public section

universe u v w vS

namespace CategoryTheory

open Functor

variable {C : Type u} [Category.{v} C]

namespace FiberedCategoryOver.Groupoids

/-- A category fibred in groupoids is representable if and only if it is fibred in setoids and
its presheaf of fiberwise isomorphism classes is representable. -/
@[stacks 02Y3 "(1)"]
theorem IsRepresentable.iff_inSetoids_and_fiberClasses
    (P : FiberedCategoryOver.Groupoids C) :
    P.IsRepresentable ↔
      Functor.IsFibered.InSetoids P.p ∧
        (Functor.fiberIsoClassPresheaf P.p).IsRepresentable := sorry

/-- A representable category fibred in groupoids is fibred in setoids. -/
theorem IsRepresentable.inSetoids
    {P : FiberedCategoryOver.Groupoids C}
    (hP : P.IsRepresentable) :
    Functor.IsFibered.InSetoids P.p := sorry

/-- The fiberwise-iso-class presheaf of a representable category fibred in groupoids is
representable. -/
theorem IsRepresentable.fiberClasses
    {P : FiberedCategoryOver.Groupoids C}
    (hP : P.IsRepresentable) :
    (Functor.fiberIsoClassPresheaf P.p).IsRepresentable := sorry

/-- A category fibred in groupoids is representable once it is fibred in setoids and its
fiberwise-iso-class presheaf is representable. -/
@[stacks 02Y3 "setoid and fiber-class criterion for representability"]
theorem IsRepresentable.of_inSetoids_of_fiberClasses
    {P : FiberedCategoryOver.Groupoids C}
    (hSetoids : Functor.IsFibered.InSetoids P.p)
    (hClasses : (Functor.fiberIsoClassPresheaf P.p).IsRepresentable) :
    P.IsRepresentable := sorry

/-- Lifted representability is equivalent to being fibred in setoids with representable
fiberwise-isomorphism-class presheaf in every saturated fixed owner. -/
theorem IsRepresentable.Lifted.iff_inSetoids_and_fiberClasses
    (P : FiberedCategoryOver.Groupoids.{u, v,
      max w (max u v), max vS v} C) :
    IsRepresentable.Lifted P ↔
      Functor.IsFibered.InSetoids P.p ∧
        (Functor.fiberIsoClassPresheaf P.p).IsRepresentable := sorry

/-- A lifted-representable category fibred in groupoids is fibred in setoids. -/
theorem IsRepresentable.Lifted.inSetoids
    {P : FiberedCategoryOver.Groupoids.{u, v,
      max w (max u v), max vS v} C}
    (hP : IsRepresentable.Lifted P) :
    Functor.IsFibered.InSetoids P.p := sorry

/-- The fiberwise-isomorphism-class presheaf of a lifted-representable category fibred in
groupoids is representable. -/
theorem IsRepresentable.Lifted.fiberClasses
    {P : FiberedCategoryOver.Groupoids.{u, v,
      max w (max u v), max vS v} C}
    (hP : IsRepresentable.Lifted P) :
    (Functor.fiberIsoClassPresheaf P.p).IsRepresentable := sorry

/-- A category in a saturated fixed owner is lifted-representable when it is fibred in setoids and
its fiberwise-isomorphism-class presheaf is representable. -/
theorem IsRepresentable.Lifted.of_inSetoids_of_fiberClasses
    {P : FiberedCategoryOver.Groupoids.{u, v,
      max w (max u v), max vS v} C}
    (hSetoids : Functor.IsFibered.InSetoids P.p)
    (hClasses : (Functor.fiberIsoClassPresheaf P.p).IsRepresentable) :
    IsRepresentable.Lifted P := sorry

end FiberedCategoryOver.Groupoids

end CategoryTheory
