module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.Sheafification
public import ReasLib.CategoryTheory.Sites.WeaklyContractible
import Mathlib.Tactic.CrossRefAttribute

/-!
# Sheafification on the small pro-étale site

The sheafification unit of a finite-product-preserving presheaf is an isomorphism
on affine weakly contractible objects.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ProEt

/-- The sheafification unit of a finite-product-preserving Type-valued presheaf on
the small pro-étale site of a scheme is an isomorphism on every affine weakly
contractible object. -/
@[stacks 0F63]
instance toSheafify_app_isIso
    {X : Scheme.{u}} [HasWeakSheafify (topology X) (Type (u + 1))]
    (F : X.ProEtᵒᵖ ⥤ Type (u + 1)) [PreservesFiniteProducts F]
    {W : X.ProEt} [IsAffine W.left] [(topology X).IsWeaklyContractible W] :
    IsIso ((toSheafify (topology X) F).app (op W)) :=
  sorry

/-- The sheafification unit of a finite-product-preserving Type-valued
presheaf on `X.ProEt` is bijective on sections over an affine weakly
contractible object. -/
theorem bijective_toSheafify_app
    {X : Scheme.{u}} [HasWeakSheafify (topology X) (Type (u + 1))]
    (F : X.ProEtᵒᵖ ⥤ Type (u + 1)) [PreservesFiniteProducts F]
    {W : X.ProEt} [IsAffine W.left] [(topology X).IsWeaklyContractible W] :
    Function.Bijective ((toSheafify (topology X) F).app (op W)) :=
  (CategoryTheory.isIso_iff_bijective _).mp (toSheafify_app_isIso F)

end AlgebraicGeometry.Scheme.ProEt
