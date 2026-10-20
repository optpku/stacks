/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Annihilator
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.InternalHom.Coherent
import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent.Closure
import Mathlib.Tactic.CrossRefAttribute

/-!
# Coherence of annihilator sheaves

The annihilator is already owned as the kernel of the scalar-action map.  This leaf records the
canonical coherence consequence and depends only on the generic coherent-kernel and internal-Hom
owners.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalClosed
open AlgebraicGeometry

noncomputable section

universe u

namespace SheafOfModules.Annihilator

variable {X : RingedSpace.{u}}

open scoped Annihilator

/-- If the structure module and `F` are coherent, then the annihilator sheaf of `F` is
coherent. -/
@[stacks 0H2L, instance]
theorem isCoherent (F : X.Modules)
    [(SheafOfModules.unit X.ringCatSheaf : X.Modules).IsCoherent]
    [F.IsCoherent] : (Ann(F)).IsCoherent := sorry

end SheafOfModules.Annihilator
