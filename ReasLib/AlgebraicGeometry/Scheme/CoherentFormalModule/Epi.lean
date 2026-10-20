/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Category

/-!
# Epimorphisms of coherent formal modules

This file characterizes epimorphisms of coherent formal modules through their first-stage
components.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/-- A morphism of coherent formal modules over a Noetherian scheme is an epimorphism exactly
when its component at the first stage is an epimorphism. -/
theorem coherentFormalModules_epi_iff_firstStage_epi
    {X : Scheme.{u}} [IsNoetherian X] {I : X.IdealSheafData}
    {F G : CoherentFormalModules X I} (φ : F ⟶ G) :
    Epi φ ↔ Epi (φ.hom.app (Opposite.op 1)) := sorry

end AlgebraicGeometry.Scheme
