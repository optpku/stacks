module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ExtensionByZero

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u w

namespace AlgebraicGeometry.Scheme

variable {U X : Scheme.{u}}

/-- The trace natural transformation for étale sheaves of abelian groups is the
counit of extension by zero and restriction. -/
noncomputable def abelianEtaleTrace (j : U ⟶ X) [Etale j]
    [∀ G : U.Etaleᵒᵖ ⥤ AddCommGrpCat.{w},
      (etaleRestriction j).op.HasLeftKanExtension G]
    [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{w}] :
    etaleRestrictionSheaf j AddCommGrpCat.{w} ⋙ abelianExtensionByZero j ⟶
      𝟭 (Sheaf X.smallEtaleTopology AddCommGrpCat.{w}) :=
  (abelianExtensionByZero_adjunction j).counit

end AlgebraicGeometry.Scheme
