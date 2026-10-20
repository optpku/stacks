/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.PseudoCoherent.Cohomology
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Module sheaves as pseudo-coherent derived objects

For a module sheaf placed in degree zero, the first two pseudo-coherence bounds recover finite
type and finite presentation.  Both directions are named explicitly so callers need not install
proof-dependent local instances.
-/

noncomputable section

universe u

namespace SheafOfModules.IsMPseudoCoherent

variable {X : AlgebraicGeometry.RingedSpace.{u}}

/-- Lemma 20.47.10 (1): a module sheaf is `0`-pseudo-coherent exactly when it is of finite
type. -/
@[stacks 09V9 "(1)"]
theorem zero_iff_isFiniteType (F : X.Modules) :
    F.IsMPseudoCoherent 0 ↔ F.IsFiniteType := sorry

/-- A `0`-pseudo-coherent module sheaf is of finite type. -/
theorem isFiniteType {F : X.Modules} (hF : F.IsMPseudoCoherent 0) :
    F.IsFiniteType := sorry

/-- A module sheaf of finite type is `0`-pseudo-coherent. -/
theorem of_isFiniteType {F : X.Modules} (hF : F.IsFiniteType) :
    F.IsMPseudoCoherent 0 := sorry

/-- Lemma 20.47.10 (2): a module sheaf is `(-1)`-pseudo-coherent exactly when it is finitely
presented. -/
@[stacks 09V9 "(2)"]
theorem minusOne_iff_isFinitePresentation (F : X.Modules) :
    F.IsMPseudoCoherent (-1) ↔ F.IsFinitePresentation := sorry

/-- A `(-1)`-pseudo-coherent module sheaf is finitely presented. -/
theorem isFinitePresentation {F : X.Modules} (hF : F.IsMPseudoCoherent (-1)) :
    F.IsFinitePresentation := sorry

/-- A finitely presented module sheaf is `(-1)`-pseudo-coherent. -/
theorem of_isFinitePresentation {F : X.Modules} (hF : F.IsFinitePresentation) :
    F.IsMPseudoCoherent (-1) := sorry

end SheafOfModules.IsMPseudoCoherent
