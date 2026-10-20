/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.LeftDerived.Canonical
public import Mathlib.CategoryTheory.Abelian.LeftDerived
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Basic Properties of Bounded-Above Left Derived Functors

This leaf contains the degree bounds and degree-zero right-exactness
consequences of a chosen bounded-above left-derived functor, together with
specializations to the canonical total-derived model.
-/

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe w vA vB uA uB

namespace CategoryTheory.Functor

variable {A : Type uA} {B : Type uB}
  [Category.{vA} A] [Category.{vB} B]
  [Abelian A] [Abelian B]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
  (F : A ⥤ B) [F.Additive]
  (LF : DerivedCategory.Minus A ⥤ DerivedCategory.Minus B)
  (ε : DerivedCategory.Minus.Qh A ⋙ LF ⟶ F.toBoundedAboveDerived)
  [LF.IsLeftDerivedFunctor ε (HomotopyCategory.Minus.quasiIso A)]

namespace LeftDerived.degree

include F ε

/-- A bounded-above left-derived functor has no positive cohomological
degrees on degree-zero objects. -/
@[stacks 05TD "dual bounded-above left-derived degree bound"]
theorem isZero_of_pos (i : ℤ) (hi : 0 < i) :
    IsZero (LeftDerived.degree LF i) := sorry

end LeftDerived.degree

include F ε

/-- Degree zero of a bounded-above left-derived functor is right exact. -/
@[stacks 05TD "dual bounded-above left-derived right exactness"]
theorem LeftDerived.zero.preservesFiniteColimits :
    PreservesFiniteColimits (LeftDerived.degree LF 0) := sorry

/-- The degree-zero comparison is invertible exactly when the original
additive functor is right exact. -/
@[stacks 05TD "dual bounded-above left-derived comparison criterion"]
theorem LeftDerived.zero.isIso_iff_preservesFiniteColimits :
    IsIso (LeftDerived.zero F LF ε) ↔ PreservesFiniteColimits F := sorry

omit ε

namespace LeftDerived.Bounded

variable [F.toBoundedAboveDerived.HasLeftDerivedFunctor
  (HomotopyCategory.Minus.quasiIso A)]

/-- The canonical bounded-above left-derived functor has no positive
cohomological degrees. -/
@[stacks 05TD "dual bounded-above left-derived degree bound"]
theorem degree.isZero_of_pos (i : ℤ) (hi : 0 < i) :
    IsZero (degree F i) := sorry

/-- Degree zero of the canonical bounded-above left-derived functor is right
exact. -/
@[stacks 05TD "dual bounded-above left-derived right exactness"]
theorem zero.preservesFiniteColimits :
    PreservesFiniteColimits (degree F 0) := sorry

/-- Degree zero of the canonical bounded-above left-derived functor is right exact as a
typeclass instance. -/
@[stacks 05TD "canonical bounded left-derived degree-zero instance"]
instance degree.preservesFiniteColimits : PreservesFiniteColimits (degree F 0) := sorry

/-- The canonical degree-zero comparison is invertible exactly when the
underived functor is right exact. -/
@[stacks 05TD "dual bounded-above left-derived comparison criterion"]
theorem zero.isIso_iff_preservesFiniteColimits :
    IsIso (zero F) ↔ PreservesFiniteColimits F := sorry

/-- For a right exact functor, the canonical bounded-above degree-zero comparison is an
isomorphism available to typeclass search. -/
@[stacks 05TD "canonical bounded left-derived comparison instance"]
instance zero.isIso [PreservesFiniteColimits F] : IsIso (zero F) := sorry

end LeftDerived.Bounded

end CategoryTheory.Functor
