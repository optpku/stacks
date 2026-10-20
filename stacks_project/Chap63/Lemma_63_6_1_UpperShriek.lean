/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.UpperShriek.LocallyQuasiFinite

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.GeometricPoint
open AlgebraicGeometry.Scheme.Etale

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
variable [LocallyQuasiFinite f] [LocallyOfFiniteType f]
variable [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]

/- The non-derived compact-support adjunction on abelian étale sheaves. -/
#check (AlgebraicGeometry.Scheme.Etale.lowerShriekAdjunction f :
  lowerShriek f ⊣ upperShriek f)

variable (ybar : GeometricPoint Y)
variable [HasProducts.{u} AddCommGrpCat.{u}]

/- The fibrewise skyscraper formula for non-derived upper shriek. -/
#check (AlgebraicGeometry.Scheme.Etale.upperShriekSkyscraperIso f ybar :
  (toSmallEtalePoint ybar).skyscraperSheafFunctor ⋙ upperShriek f ≅
    abelianSkyscraperProduct f ybar)

end
