module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.LocallyPrincipal
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ClosedImmersion.Complement

/-!
# Complements of locally principal closed subschemes

This file records affineness of the open complement of a locally principal closed subscheme.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.IsLocallyPrincipalClosedSubscheme

/-- The inclusion of the open complement of a locally principal closed subscheme is affine. -/
instance isAffineHom_closedImmersionComplement {S Z : Scheme.{u}} (i : Z ⟶ S)
    [IsLocallyPrincipalClosedSubscheme i] :
    IsAffineHom (closedImmersionComplement i).ι := sorry

end AlgebraicGeometry.IsLocallyPrincipalClosedSubscheme
