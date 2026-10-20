/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.WeaklyEtale.Locality
public import ReasLib.RingTheory.Etale.Weakly.AbsolutelyFlat

/-!
# Reduced sources of weakly étale morphisms

This module records ascent of reducedness along weakly étale morphisms of schemes.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.WeaklyEtale

/-- The source of a weakly étale morphism with reduced target is reduced. -/
@[stacks 094Y]
theorem isReduced {X Y : Scheme.{u}} (f : X ⟶ Y) [WeaklyEtale f] [IsReduced Y] :
    IsReduced X := sorry

end AlgebraicGeometry.WeaklyEtale
