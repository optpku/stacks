/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.FiniteSupport.OpenImmersion
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LowerShriek.LocallyQuasiFinite.OpenImmersion

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

/-- The forward map of the finite-support comparison isomorphism. -/
def lowerShriekPresheafIsoHom {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsSeparated f] [LocallyQuasiFinite f] [LocallyOfFiniteType f] :
    lowerShriekPresheaf f ⟶
      etaleLowerShriek f ⋙
        sheafToPresheaf Y.smallEtaleTopology AddCommGrpCat.{u} :=
  (lowerShriekPresheafIso f).hom

end AlgebraicGeometry.Scheme.Etale

variable {X' X Y : Scheme.{u}} (j : X' ⟶ X) (f : X ⟶ Y)
variable [IsOpenImmersion j] [LocallyQuasiFinite f]

/- Finite-support covariance along an open immersion of the source. -/
#check (AlgebraicGeometry.Scheme.Etale.lowerShriekPresheafOpenImmersion j f :
  etaleRestrictionSheaf j AddCommGrpCat.{u} ⋙ lowerShriekPresheaf (j ≫ f) ⟶
    lowerShriekPresheaf f)

variable [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]

/- Sheafification gives covariance of compact-support direct images. -/
#check (AlgebraicGeometry.Scheme.Etale.lowerShriekOpenImmersion j f :
  etaleRestrictionSheaf j AddCommGrpCat.{u} ⋙ lowerShriek (j ≫ f) ⟶ lowerShriek f)

end

end
