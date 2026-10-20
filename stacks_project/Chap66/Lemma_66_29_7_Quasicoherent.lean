/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Quasicoherent.Limits

/-! # Closure properties of quasi-coherent algebraic-space modules

The public owner preserves all actual categorical and tensor/internal-Hom statements.
The original source lemma facade retains its independent tag coverage.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.MonoidalClosed CategoryTheory.ObjectProperty
open AlgebraicGeometry
open scoped SheafOfModules.RingedSite

universe u v w

namespace AlgebraicGeometry.AlgebraicSpace

#check (AlgebraicGeometry.AlgebraicSpace.modulesAbelian :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S), Abelian (Modules X))

#check
  (AlgebraicGeometry.AlgebraicSpace.QCoh.closedUnderColimitsOfShape :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S) (J : Type v) [Category.{w} J],
      (quasiCoherentModuleProperty X).IsClosedUnderColimitsOfShape J)

#check
  (AlgebraicGeometry.AlgebraicSpace.QCoh.isWeakSerreClass :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
      (quasiCoherentModuleProperty X).IsWeakSerreClass)

#check
  (AlgebraicGeometry.AlgebraicSpace.Modules.isQuasicoherent_kernel :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {F G : X.Modules}
      [F.IsQuasicoherent] [G.IsQuasicoherent] (f : F ⟶ G),
      (kernel f).IsQuasicoherent)

#check
  (AlgebraicGeometry.AlgebraicSpace.Modules.isQuasicoherent_cokernel :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {F G : X.Modules}
      [F.IsQuasicoherent] [G.IsQuasicoherent] (f : F ⟶ G),
      (cokernel f).IsQuasicoherent)

#check
  (AlgebraicGeometry.AlgebraicSpace.Modules.isQuasicoherent_tensor :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
      (F G : SheafOfModules.RingedSite.ringedSiteModuleCategory.{u + 1, u, u, u}
        (smallEtaleTopology X) (commStructureSheaf X))
      [F.IsQuasicoherent] [G.IsQuasicoherent],
      (SheafOfModules.RingedSite.moduleTensor F G).IsQuasicoherent)

#check
  (AlgebraicGeometry.AlgebraicSpace.Modules.isQuasicoherent_internalHom :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
      (F G : SheafOfModules.RingedSite.ringedSiteModuleCategory.{u + 1, u, u + 1, u + 1}
        (smallEtaleTopology X) (commStructureSheafLift X))
      [F.IsFinitePresentation] [G.IsQuasicoherent],
      ((ihom F).obj G).IsQuasicoherent)

end AlgebraicGeometry.AlgebraicSpace
