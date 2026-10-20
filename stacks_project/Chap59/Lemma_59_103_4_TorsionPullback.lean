module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.H.EtaleCohomology

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.HComparison

/-- Sheafification exists for abelian presheaves on the small étale site with coefficients
in the universe one level above the scheme. -/
instance smallEtale_hasSheafify_addCommGrp (X : Scheme.{u}) :
    CategoryTheory.HasSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1} := by
  infer_instance

/-- Inverse image on abelian sheaves from the small étale site of a scheme to its
big étale slice, expressed through identity-base étale relocalization. -/
abbrev piInverseImage (X : Scheme.{u}) := FppfEtale.piInverseImage X

end AlgebraicGeometry.Scheme.HComparison

end

end
