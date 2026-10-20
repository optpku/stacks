/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.FinitePresentation
import StacksCheckRecall

universe u

/- Lemma 28.22.7: for a quasi-compact quasi-separated scheme `X`, every quasi-coherent
`F : X.Modules` is a filtered colimit of modules of finite presentation. The predicate
`ObjectProperty.ind` supplies a small filtered category, a diagram in `X.Modules`, and a
`ColimitPresentation`; its cocone legs are the maps to `F`, its naturality records compatibility
with the transition maps, and its colimit witness identifies the apex with `F`.
-/
@[stacks 01PK] #check
  (AlgebraicGeometry.Scheme.Modules.isFinitePresentation_ind :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
      (F : X.Modules) [F.IsQuasicoherent],
      (SheafOfModules.isFinitePresentation X.ringCatSheaf).ind.{u} F)
