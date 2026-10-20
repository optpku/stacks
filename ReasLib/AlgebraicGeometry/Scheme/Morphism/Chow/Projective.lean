/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Chow
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Constructors

/-!
# Projectivity of Chow modifications

This file records the projectivity property of the morphism underlying a Chow modification.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.ChowLemmaModification

/-- The morphism from a Chow modification to the original scheme is H-projective. -/
theorem hProjective {X S : Scheme.{u}} {f : X ⟶ S} (M : ChowLemmaModification f) :
    HProjective M.π := sorry

end AlgebraicGeometry.ChowLemmaModification
