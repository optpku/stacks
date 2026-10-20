module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.FiniteSupport.Presheaf

/-!
# Compact-support lower shriek as a colimit of `H_Z(F)`

The abelian presheaf `f_p! F` on `Y_étale`, with values the colimit of
supported sections `H_Z(F)` over admissible locally closed subsets of `|X_V|`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyQuasiFinite f]

/- The finite-support presheaf of abelian groups. -/
#check (AlgebraicGeometry.Scheme.Etale.lowerShriekPresheaf f :
  Sheaf X.smallEtaleTopology AddCommGrpCat.{u} ⥤
    Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{u})

end
