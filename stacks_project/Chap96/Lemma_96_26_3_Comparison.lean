module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Derived.AffineEtale

/-!
# Affine étale comparison of the chaotic affine site

The affine projection and the canonical affine étale comparison are available from their
mathematical owners.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

#check (AlgebraicGeometry.GroupoidsOver.affineSiteToAffineOver :
  {S : Scheme.{u}} → (X : GroupoidsOver S) →
    AlgebraicGeometry.GroupoidsOver.affineSite X ⥤ S.AffineOver)
