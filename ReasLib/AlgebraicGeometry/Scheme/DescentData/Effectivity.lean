/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.EssentialImage
public import ReasLib.AlgebraicGeometry.Scheme.DescentData

/-!
# Effective scheme descent data

Effectivity is expressed as membership in the essential image of the canonical
pullback descent functor.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace AlgebraicGeometry.Scheme.DescentData

variable {I : Type v} {S : Scheme.{u}}
variable {X : I → Scheme.{u}} {f : ∀ i, X i ⟶ S}

/-- A scheme descent datum is effective when it lies in the essential image of the
canonical pullback descent functor. -/
abbrev IsEffective (D : DescentData X f) : Prop :=
  (overPseudofunctor.toDescentData f).essImage D

/-- A scheme descent datum is effective exactly when it is isomorphic to the canonical
pullback datum of some scheme over the base. -/
theorem isEffective_iff (D : DescentData X f) :
    D.IsEffective ↔ ∃ U : Over S, Nonempty (ofObj X f U ≅ D) := sorry

namespace IsEffective

/-- The canonical pullback descent datum of a scheme over the base is effective. -/
theorem ofObj (U : Over S) : IsEffective (DescentData.ofObj X f U) := sorry

/-- Effectivity is preserved by isomorphisms of scheme descent data. -/
theorem ofIso {D E : DescentData X f} (e : D ≅ E) (hD : IsEffective D) :
    IsEffective E := sorry

end IsEffective

end AlgebraicGeometry.Scheme.DescentData
