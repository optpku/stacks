module

public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Sites.Whiskering

/-!
# Sheafification on affine étale slice sites

Successor-universe additive sheafification and sheaf composition on slices of
small affine étale sites.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.AffineEtale

/-- Slice sites of the small affine étale topology support composition with the
ring-to-abelian-group forgetful functor in universe `u + 1`. -/
instance over_hasSheafCompose_succ (U : Scheme.{u})
    (V : U.AffineEtale) :
    ((AffineEtale.topology U).over V).HasSheafCompose
      (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1}) :=
  sorry

/-- Additive sheafification exists on every slice of a small affine étale site
in universe `u + 1`. -/
instance over_hasWeakSheafify_succ (U : Scheme.{u})
    (V : U.AffineEtale) :
    HasWeakSheafify ((AffineEtale.topology U).over V) AddCommGrpCat.{u + 1} :=
  sorry

/-- On every affine étale slice, sheafification equivalences in universe
`u + 1` are the locally bijective morphisms. -/
instance over_wEqualsLocallyBijective_succ (U : Scheme.{u})
    (V : U.AffineEtale) :
    ((AffineEtale.topology U).over V).WEqualsLocallyBijective
      AddCommGrpCat.{u + 1} :=
  sorry


end AlgebraicGeometry.Scheme.AffineEtale
