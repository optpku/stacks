/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.WeaklyAssociatedPoints
import Mathlib.Tactic.CrossRefAttribute

/-!
# Weakly associated points of schemes

This file specializes weakly associated points of scheme modules to the
structure sheaf.
-/

@[expose] public section

open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

open AlgebraicGeometry.RingedSpace

variable (X : Scheme.{u})

/-- The weakly associated points of a scheme are those of its structure sheaf. -/
@[stacks 056L]
abbrev weakAss : Set X :=
  Scheme.Modules.weakAss (SheafOfModules.unit X.ringCatSheaf : X.Modules)

/-- Membership in the weakly associated points of a scheme is membership for its structure
sheaf. -/
theorem mem_weakAss_iff (x : X) :
    x ∈ X.weakAss ↔ Scheme.Modules.weaklyAssociatedAt
      (SheafOfModules.unit X.ringCatSheaf : X.Modules) x :=
  Scheme.Modules.mem_weakAss_iff
    (SheafOfModules.unit X.ringCatSheaf : X.Modules) x

/-- Membership in the weakly associated points of a scheme is the weak-association condition for
the maximal ideal of its structure-sheaf stalk. -/
theorem mem_weakAss_iff_isWeaklyAssociatedToModule (x : X) :
    x ∈ X.weakAss ↔
      Ideal.IsWeaklyAssociatedToModule (X.presheaf.stalk x)
        (RingedSpace.stalkModuleCat
          (SheafOfModules.unit X.ringCatSheaf : X.Modules) x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) :=
  Scheme.Modules.mem_weakAss_iff
    (SheafOfModules.unit X.ringCatSheaf : X.Modules) x

end AlgebraicGeometry.Scheme
