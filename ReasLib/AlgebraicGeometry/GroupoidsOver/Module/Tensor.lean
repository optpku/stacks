/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Associated
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.FlatBaseChange

/-! # Tensor products of fppf modules -/

@[expose] public section

open CategoryTheory
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} {X : GroupoidsOver S}

/-- The tensor product of fppf modules, transported from the commutative fppf presentation. -/
def moduleTensorFppf (H F : fppfModules X) : fppfModules X :=
  (fromCommAssociatedModules X).obj
    (moduleTensorAssociated ((toCommAssociatedModules X .fppf).obj H)
      ((toCommAssociatedModules X .fppf).obj F))

/-- The morphism on fppf tensor products induced by morphisms in both factors. -/
def moduleTensorFppfMap {H H' F F' : fppfModules X} (h : H ⟶ H') (f : F ⟶ F') :
    moduleTensorFppf H F ⟶ moduleTensorFppf H' F' :=
  (fromCommAssociatedModules X).map
    (@SheafOfModules.RingedSite.moduleTensorMap.{u + 1, u, u}
      X.total inferInstance (X.associatedTopology .fppf)
      (associatedTopology_hasSheafCompose_commRing X .fppf)
      (associatedTopology_hasWeakSheafify X .fppf) (associatedTopology_wEqualsLocallyBijective X .fppf)
      (commAssociatedStructureSheaf X .fppf)
      ((toCommAssociatedModules X .fppf).obj H) ((toCommAssociatedModules X .fppf).obj H')
      ((toCommAssociatedModules X .fppf).obj F) ((toCommAssociatedModules X .fppf).obj F')
      ((toCommAssociatedModules X .fppf).map h) ((toCommAssociatedModules X .fppf).map f))

end AlgebraicGeometry.GroupoidsOver
