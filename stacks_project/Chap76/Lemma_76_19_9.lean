/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.LocallyProjective.EtaleCohomology

open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.AssociatedModule

universe u

/- Lemma 76.19.9 -/
@[stacks 061J] #check
  (AlgebraicGeometry.Scheme.AssociatedModule.etaleInternalHom_firstCohomology_isZero :
    ∀ {T : Scheme.{u}} [IsAffine T] (F G : T.Modules)
    [F.IsQuasicoherent] [G.IsQuasicoherent] [IsLocallyProjective F]
    [HasSheafify (StandardTopology.Small.topology .etale T) AddCommGrpCat.{u + 1}]
    [HasExt.{u + 1}
      (Sheaf (StandardTopology.Small.topology .etale T) AddCommGrpCat.{u + 1})],
    IsZero
      ((Sheaf.functorH (StandardTopology.Small.topology .etale T) 1).obj
        ((SheafOfModules.toSheaf.{u + 1} _).obj
          (SheafOfModules.RingedSite.InternalHom.obj.{u + 1, u, u + 1}
            (StandardSmall.commStructureSheaf .etale T)
            (StandardSmall.comm .etale T F) (StandardSmall.comm .etale T G)))))
