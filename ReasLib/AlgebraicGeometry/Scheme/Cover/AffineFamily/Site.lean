module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.AffineFamily

/-!
# Affine families from site families

This module converts finite families in a slice category, viewed through a
scheme-valued functor, into finite affine families over the image of their target.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe w v u

namespace AlgebraicGeometry.AffineFamilyOver

variable {C : Type u} [Category.{v} C]

/-- Convert a finite family in a slice into the corresponding finite affine family of schemes. -/
def ofSiteFamily (p : C ⥤ Scheme.{w}) (U : C) (n : ℕ)
    (family : Fin n → Over U) (h_affine : ∀ i, IsAffine (p.obj (family i).left)) :
    AffineFamilyOver (p.obj U) where
  n := n
  U := fun i ↦ p.obj (family i).left
  map := fun i ↦ p.map (family i).hom
  isAffine := h_affine

/-- The schemes in `ofSiteFamily` are the images of the source objects of the site family. -/
theorem ofSiteFamily_U (p : C ⥤ Scheme.{w}) (U : C) (n : ℕ)
    (family : Fin n → Over U) (h_affine : ∀ i, IsAffine (p.obj (family i).left))
    (i : Fin n) :
    (ofSiteFamily p U n family h_affine).U i = p.obj (family i).left := sorry

/-- The maps in `ofSiteFamily` are obtained by applying the scheme-valued functor to the
site-family arrows. -/
theorem ofSiteFamily_map (p : C ⥤ Scheme.{w}) (U : C) (n : ℕ)
    (family : Fin n → Over U) (h_affine : ∀ i, IsAffine (p.obj (family i).left))
    (i : Fin n) :
    (ofSiteFamily p U n family h_affine).map i = p.map (family i).hom := sorry

end AlgebraicGeometry.AffineFamilyOver
