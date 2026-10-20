/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.DifferentialOperator.Derived.RelativeCupProduct

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.RelativeCupProduct

open Modules.Kunneth

variable {Z W : Scheme.{u}} (f : Z ⟶ W)

/- The relative cup-product construction is provided by its reusable mathematical owner. -/
#check AlgebraicGeometry.Scheme.RelativeCupProduct.map

end AlgebraicGeometry.Scheme.RelativeCupProduct

end
