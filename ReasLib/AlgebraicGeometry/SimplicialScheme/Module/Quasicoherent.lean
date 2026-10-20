/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.SimplicialScheme.Module.Pullback
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

/-!
# Quasi-coherence under pullback on simplicial schemes
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.SimplicialObject

/-- Pullback along a morphism of simplicial schemes preserves quasi-coherent modules
on their Zariski sites. -/
instance modulePullback_isQuasicoherent {V U : SimplicialObject Scheme.{u}} (f : V ⟶ U)
    (F : SheafOfModules.{u} (structureSheaf U)) [F.IsQuasicoherent] :
    ((modulePullback f).obj F).IsQuasicoherent :=
  sorry

end AlgebraicGeometry.SimplicialObject
