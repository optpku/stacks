/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Differentials.ExteriorPower.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Module.Reflexive.Determinant

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.RelativeDifferentials

/-- The canonical comparison from pulled-back differential determinants to the reflexive
determinant of the composite relative differential sheaf. -/
noncomputable def reflexiveDeterminantComparison {X S T : Scheme.{u}}
    (f : X ⟶ S) (g : S ⟶ T) (r : ℕ) :
    (Scheme.Modules.pullback f).obj (Λ[r] Ω[g.toShHom]) ⟶
      Scheme.Modules.ReflexiveDeterminant.sheaf r Ω[(f ≫ g).toShHom] :=
  formComparison (CommSq.mk (Category.comp_id (f ≫ g)).symm) r ≫
    Scheme.Modules.toReflexiveHull (Λ[r] Ω[(f ≫ g).toShHom])

end AlgebraicGeometry.Scheme.RelativeDifferentials
