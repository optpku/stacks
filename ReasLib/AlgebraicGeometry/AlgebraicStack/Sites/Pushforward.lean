module

public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Sites.PrimedFibreProduct

/-!
# Pushforward along restricted lisse-étale and flat-fppf site functors

Evaluation of sheaf pushforward is identified with global sections on the
primed Yoneda fibre product through the concrete restricted projection.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Functor Limits Opposite
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}} {X Y : GroupoidsOver S}
variable [AlgebraicStack X] [AlgebraicStack Y]

/-- The forward map of the identification
`f'_* H(y) ⟶ Γ((V ×_{y,Y} X)', (pr')⁻¹ H)` on the lisse-étale site, obtained by
evaluating the pointwise right Kan extension as a comma limit and reindexing
along `lisseYonedaFibreProduct.toStructuredArrow`. -/
def lisseEtalePushforwardObjIsoGlobalSectionsHom (f : X ⟶ Y) [Smooth f]
    (H : Sheaf (lisseEtaleTopology X) (Type (u + 1))) (y : lisseEtaleSite Y)
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type (u + 1),
      (lisseEtaleMap f).op.HasPointwiseRightKanExtension P]
    [HasLimit ((lisseYonedaFibreProduct.pr f y).op ⋙ H.obj)] :
    (((lisseEtaleMap f).sheafPushforwardCocontinuous (Type (u + 1))
        (lisseEtaleTopology X) (lisseEtaleTopology Y)).obj H).obj.obj (op y) ⟶
      limit ((lisseYonedaFibreProduct.pr f y).op ⋙ H.obj) :=
  ((lisseEtaleMap f).op.ranObjObjIsoLimit H.obj (op y)).hom ≫
    limit.pre (StructuredArrow.proj (op y) (lisseEtaleMap f).op ⋙ H.obj)
      (lisseYonedaFibreProduct.toStructuredArrow f y)

/-- The canonical comparison from pushforward evaluation to primed global
sections is invertible. -/
instance lisseEtalePushforwardObjIsoGlobalSections.isIso (f : X ⟶ Y) [Smooth f]
    (H : Sheaf (lisseEtaleTopology X) (Type (u + 1))) (y : lisseEtaleSite Y)
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type (u + 1),
      (lisseEtaleMap f).op.HasPointwiseRightKanExtension P]
    [HasLimit ((lisseYonedaFibreProduct.pr f y).op ⋙ H.obj)] :
    IsIso (lisseEtalePushforwardObjIsoGlobalSectionsHom f H y) := sorry

/-- Evaluation of sheaf pushforward on the lisse-étale site is canonically
isomorphic to the limit of the sheaf pulled back along the primed projection. -/
def lisseEtalePushforwardObjIsoGlobalSections (f : X ⟶ Y) [Smooth f]
    (H : Sheaf (lisseEtaleTopology X) (Type (u + 1))) (y : lisseEtaleSite Y)
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type (u + 1),
      (lisseEtaleMap f).op.HasPointwiseRightKanExtension P]
    [HasLimit ((lisseYonedaFibreProduct.pr f y).op ⋙ H.obj)] :
    (((lisseEtaleMap f).sheafPushforwardCocontinuous (Type (u + 1))
        (lisseEtaleTopology X) (lisseEtaleTopology Y)).obj H).obj.obj (op y) ≅
      limit ((lisseYonedaFibreProduct.pr f y).op ⋙ H.obj) :=
  asIso (lisseEtalePushforwardObjIsoGlobalSectionsHom f H y)

/-- The identification `f'_* H(y) ≅ Γ((V ×_{y,Y} X)', (pr')⁻¹ H)` computes on
an object `q` of the primed 2-fibre product as the limit projection of
`(pr')⁻¹ H` at `pr'(q)`. -/
theorem lisseEtalePushforwardObjIsoGlobalSections_π (f : X ⟶ Y) [Smooth f]
    (H : Sheaf (lisseEtaleTopology X) (Type (u + 1))) (y : lisseEtaleSite Y)
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type (u + 1),
      (lisseEtaleMap f).op.HasPointwiseRightKanExtension P]
    [HasLimit ((lisseYonedaFibreProduct.pr f y).op ⋙ H.obj)]
    (q : lisseYonedaFibreProduct f y) :
    (lisseEtalePushforwardObjIsoGlobalSections f H y).hom ≫
        limit.π ((lisseYonedaFibreProduct.pr f y).op ⋙ H.obj) (op q) =
      (((lisseEtaleMap f).sheafPushforwardCocontinuous (Type (u + 1))
            (lisseEtaleTopology X) (lisseEtaleTopology Y)).obj H).obj.map
          (op (lisseYonedaFibreProduct.arrow f y q)) ≫
        ((lisseEtaleMap f).op.ranCounit.app H.obj).app
          (op ((lisseYonedaFibreProduct.pr f y).obj q)) :=
  sorry

/-- The identification `f'_* H(y) ≅ Γ((V ×_{y,Y} X)', (pr')⁻¹ H)` is natural in
the sheaf `H`. -/
theorem lisseEtalePushforwardObjIsoGlobalSections_natural (f : X ⟶ Y) [Smooth f]
    {H G : Sheaf (lisseEtaleTopology X) (Type (u + 1))} (τ : H ⟶ G)
    (y : lisseEtaleSite Y)
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type (u + 1),
      (lisseEtaleMap f).op.HasPointwiseRightKanExtension P]
    [HasLimit ((lisseYonedaFibreProduct.pr f y).op ⋙ H.obj)]
    [HasLimit ((lisseYonedaFibreProduct.pr f y).op ⋙ G.obj)] :
    (lisseEtalePushforwardObjIsoGlobalSections f H y).hom ≫
        limMap (whiskerLeft (lisseYonedaFibreProduct.pr f y).op
          ((sheafToPresheaf (lisseEtaleTopology X) (Type (u + 1))).map τ)) =
      (((lisseEtaleMap f).sheafPushforwardCocontinuous (Type (u + 1))
            (lisseEtaleTopology X) (lisseEtaleTopology Y)).map τ).hom.app (op y) ≫
        (lisseEtalePushforwardObjIsoGlobalSections f G y).hom :=
  sorry

/-- The forward map of the identification
`f'_* H(y) ⟶ Γ((V ×_{y,Y} X)', (pr')⁻¹ H)` on the flat-fppf site. -/
def flatFppfPushforwardObjIsoGlobalSectionsHom (f : X ⟶ Y) [Flat f]
    (H : Sheaf (flatFppfTopology X) (Type (u + 1))) (y : flatFppfSite Y)
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type (u + 1),
      (flatFppfMap f).op.HasPointwiseRightKanExtension P]
    [HasLimit ((flatYonedaFibreProduct.pr f y).op ⋙ H.obj)] :
    (((flatFppfMap f).sheafPushforwardCocontinuous (Type (u + 1))
        (flatFppfTopology X) (flatFppfTopology Y)).obj H).obj.obj (op y) ⟶
      limit ((flatYonedaFibreProduct.pr f y).op ⋙ H.obj) :=
  ((flatFppfMap f).op.ranObjObjIsoLimit H.obj (op y)).hom ≫
    limit.pre (StructuredArrow.proj (op y) (flatFppfMap f).op ⋙ H.obj)
      (flatYonedaFibreProduct.toStructuredArrow f y)

/-- The canonical comparison from pushforward evaluation to primed global
sections is invertible. -/
instance flatFppfPushforwardObjIsoGlobalSections.isIso (f : X ⟶ Y) [Flat f]
    (H : Sheaf (flatFppfTopology X) (Type (u + 1))) (y : flatFppfSite Y)
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type (u + 1),
      (flatFppfMap f).op.HasPointwiseRightKanExtension P]
    [HasLimit ((flatYonedaFibreProduct.pr f y).op ⋙ H.obj)] :
    IsIso (flatFppfPushforwardObjIsoGlobalSectionsHom f H y) := sorry

/-- Evaluation of sheaf pushforward on the flat-fppf site is canonically
isomorphic to the limit of the sheaf pulled back along the primed projection. -/
def flatFppfPushforwardObjIsoGlobalSections (f : X ⟶ Y) [Flat f]
    (H : Sheaf (flatFppfTopology X) (Type (u + 1))) (y : flatFppfSite Y)
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type (u + 1),
      (flatFppfMap f).op.HasPointwiseRightKanExtension P]
    [HasLimit ((flatYonedaFibreProduct.pr f y).op ⋙ H.obj)] :
    (((flatFppfMap f).sheafPushforwardCocontinuous (Type (u + 1))
        (flatFppfTopology X) (flatFppfTopology Y)).obj H).obj.obj (op y) ≅
      limit ((flatYonedaFibreProduct.pr f y).op ⋙ H.obj) :=
  asIso (flatFppfPushforwardObjIsoGlobalSectionsHom f H y)

/-- The identification `f'_* H(y) ≅ Γ((V ×_{y,Y} X)', (pr')⁻¹ H)` on the
flat-fppf site computes on an object `q` of the primed 2-fibre product as the
limit projection of `(pr')⁻¹ H` at `pr'(q)`. -/
theorem flatFppfPushforwardObjIsoGlobalSections_π (f : X ⟶ Y) [Flat f]
    (H : Sheaf (flatFppfTopology X) (Type (u + 1))) (y : flatFppfSite Y)
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type (u + 1),
      (flatFppfMap f).op.HasPointwiseRightKanExtension P]
    [HasLimit ((flatYonedaFibreProduct.pr f y).op ⋙ H.obj)]
    (q : flatYonedaFibreProduct f y) :
    (flatFppfPushforwardObjIsoGlobalSections f H y).hom ≫
        limit.π ((flatYonedaFibreProduct.pr f y).op ⋙ H.obj) (op q) =
      (((flatFppfMap f).sheafPushforwardCocontinuous (Type (u + 1))
            (flatFppfTopology X) (flatFppfTopology Y)).obj H).obj.map
          (op (flatYonedaFibreProduct.arrow f y q)) ≫
        ((flatFppfMap f).op.ranCounit.app H.obj).app
          (op ((flatYonedaFibreProduct.pr f y).obj q)) :=
  sorry

/-- The identification `f'_* H(y) ≅ Γ((V ×_{y,Y} X)', (pr')⁻¹ H)` on the
flat-fppf site is natural in the sheaf `H`. -/
theorem flatFppfPushforwardObjIsoGlobalSections_natural (f : X ⟶ Y) [Flat f]
    {H G : Sheaf (flatFppfTopology X) (Type (u + 1))} (τ : H ⟶ G)
    (y : flatFppfSite Y)
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type (u + 1),
      (flatFppfMap f).op.HasPointwiseRightKanExtension P]
    [HasLimit ((flatYonedaFibreProduct.pr f y).op ⋙ H.obj)]
    [HasLimit ((flatYonedaFibreProduct.pr f y).op ⋙ G.obj)] :
    (flatFppfPushforwardObjIsoGlobalSections f H y).hom ≫
        limMap (whiskerLeft (flatYonedaFibreProduct.pr f y).op
          ((sheafToPresheaf (flatFppfTopology X) (Type (u + 1))).map τ)) =
      (((flatFppfMap f).sheafPushforwardCocontinuous (Type (u + 1))
            (flatFppfTopology X) (flatFppfTopology Y)).map τ).hom.app (op y) ≫
        (flatFppfPushforwardObjIsoGlobalSections f G y).hom :=
  sorry

end AlgebraicGeometry.AlgebraicStack
