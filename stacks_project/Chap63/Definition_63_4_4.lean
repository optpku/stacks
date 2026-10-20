/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LowerShriek.LocallyQuasiFinite
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyQuasiFinite f]
  [LocallyOfFiniteType f] [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]

/- Definition 63.4.4: for a locally quasi-finite morphism `f : X ⟶ Y` of
schemes, the direct image with compact support is the functor
`lowerShriek f : Ab(X_étale) ⥤ Ab(Y_étale)` given by sheafifying the abelian
presheaf `lowerShriekPresheaf f`, i.e. `f_! F = (f_{p!} F)^#`.
Stacks' locally quasi-finite hypothesis includes local finite type, so it is
rendered by `[LocallyQuasiFinite f]` together with `[LocallyOfFiniteType f]`. -/
@[stacks 0F6R] #check (AlgebraicGeometry.Scheme.Etale.lowerShriek f :
  Sheaf X.smallEtaleTopology AddCommGrpCat.{u} ⥤
    Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})

end
