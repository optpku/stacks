module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Proetale.Sheafification
import StacksCheckRecall

/-!
# Lemma 61.16.1

On an affine weakly contractible object of the small pro-étale site, the
sheafification unit of a finite-product-preserving Type-valued presheaf is an
isomorphism.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u

open AlgebraicGeometry.Scheme.ProEt

/- Lemma 61.16.1: if `X` is a scheme and `F` is a Type-valued presheaf on
the small pro-étale site `X.ProEt` which preserves finite products, then
the sheafification unit `(toSheafify (topology X) F).app (op W)` is an
isomorphism whenever `W` is an affine weakly contractible object of
`X.ProEt`. -/
@[stacks 0F63] #check (AlgebraicGeometry.Scheme.ProEt.toSheafify_app_isIso :
    ∀ {X : Scheme.{u}} [HasWeakSheafify (topology X) (Type (u + 1))]
    (F : X.ProEtᵒᵖ ⥤ Type (u + 1)) [PreservesFiniteProducts F]
    {W : X.ProEt} [IsAffine W.left] [(topology X).IsWeaklyContractible W],
    IsIso ((toSheafify (topology X) F).app (op W)))

/- The sheafification unit of a finite-product-preserving Type-valued
presheaf on `X.ProEt` is bijective on sections over an affine weakly
contractible object. -/
#check (AlgebraicGeometry.Scheme.ProEt.bijective_toSheafify_app :
    ∀ {X : Scheme.{u}} [HasWeakSheafify (topology X) (Type (u + 1))]
    (F : X.ProEtᵒᵖ ⥤ Type (u + 1)) [PreservesFiniteProducts F]
    {W : X.ProEt} [IsAffine W.left] [(topology X).IsWeaklyContractible W],
    Function.Bijective ((toSheafify (topology X) F).app (op W)))
