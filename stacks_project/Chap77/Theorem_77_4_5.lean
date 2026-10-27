/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FlatOver.Locus.WeaklyAssociated
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open TopologicalSpace

universe u

/- Theorem 77.4.5: the relative flatness locus is open. -/
@[stacks 0DLR] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.isOpen_flatOverAt_of_locallyFinite_weakAss :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [LocallyOfFinitePresentation f] (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType],
      LocallyFinite (fun y : Y.weakAss ↦ ({y.1} : Set (Points Y))) →
        IsOpen {x | Modules.flatOverAt F f x})

/- Theorem 77.4.5: the restriction to the flat locus is finitely presented. -/
@[stacks 0DLR] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.flatOverLocus_isFinitePresentation :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [LocallyOfFinitePresentation f] (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
      (h_weakAss : LocallyFinite (fun y : Y.weakAss ↦ ({y.1} : Set (Points Y)))),
      ((Modules.pullback
        (OpenSubspace.fromOpens (Modules.flatOverOpens f F h_weakAss)).ι).obj F).IsFinitePresentation)

/- Theorem 77.4.5: the restriction to the flat locus is flat over the target. -/
@[stacks 0DLR] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.flatOverLocus_isFlatOver :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [LocallyOfFinitePresentation f] (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
      (h_weakAss : LocallyFinite (fun y : Y.weakAss ↦ ({y.1} : Set (Points Y)))),
      ∀ x, Modules.flatOverAt
        ((Modules.pullback
          (OpenSubspace.fromOpens (Modules.flatOverOpens f F h_weakAss)).ι).obj F)
        ((OpenSubspace.fromOpens (Modules.flatOverOpens f F h_weakAss)).ι ≫ f) x)
