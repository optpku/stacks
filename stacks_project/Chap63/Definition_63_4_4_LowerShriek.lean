module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LowerShriek.LocallyQuasiFinite

/-!
# Direct image with compact support for locally quasi-finite morphisms

The abelian functor `f_!` is the sheafification of the compact-support
presheaf `f_{p!}`.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyQuasiFinite f]
variable [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]

/- Direct image with compact support is the sheafification of the finite-support presheaf. -/
#check (AlgebraicGeometry.Scheme.Etale.lowerShriek f :
  Sheaf X.smallEtaleTopology AddCommGrpCat.{u} ⥤
    Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})

end AlgebraicGeometry.Scheme.Etale

end
