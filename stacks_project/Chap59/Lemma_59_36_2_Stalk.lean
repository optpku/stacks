/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.InverseImageStalk

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
variable [HasWeakSheafify X.smallEtaleTopology (Type u)]
variable [∀ P : Y.Etaleᵒᵖ ⥤ Type u,
  (Scheme.smallEtalePullback f).op.HasLeftKanExtension P]
variable (xbar : Scheme.GeometricPoint X) (G : Sheaf Y.smallEtaleTopology (Type u))

/- The canonical geometric stalk comparison for inverse image on small étale sites. -/
#check (AlgebraicGeometry.Scheme.smallEtaleInverseImage_stalkIso f xbar G :
  (Scheme.GeometricPoint.toSmallEtalePoint xbar).sheafFiber.obj
    (((Scheme.smallEtalePullback f).sheafPullback (Type u)
      Y.smallEtaleTopology X.smallEtaleTopology).obj G) ≅
    (Scheme.GeometricPoint.toSmallEtalePoint
      (Scheme.smallEtaleInverseImage_imagePoint f xbar)).sheafFiber.obj G)
