module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Sites.Pushforward
import StacksCheckRecall

/-! # Pushforward on the lisse-étale and flat-fppf sites -/

@[expose] public section

open AlgebraicGeometry CategoryTheory Functor Limits Opposite
open AlgebraicGeometry.AlgebraicStack
open scoped Bicategory

universe u

/- 103.15.1.1 (1): Pushforward evaluation is global sections on the primed
Yoneda fibre product with its restricted projection. -/
@[stacks 07AU] #check (AlgebraicGeometry.AlgebraicStack.lisseEtalePushforwardObjIsoGlobalSections :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Smooth f]
    (H : Sheaf (lisseEtaleTopology X) (Type (u + 1))) (y : lisseEtaleSite Y)
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type (u + 1),
      (lisseEtaleMap f).op.HasPointwiseRightKanExtension P]
    [HasLimit ((lisseYonedaFibreProduct.pr f y).op ⋙ H.obj)],
    (((lisseEtaleMap f).sheafPushforwardCocontinuous (Type (u + 1))
        (lisseEtaleTopology X) (lisseEtaleTopology Y)).obj H).obj.obj (op y) ≅
      limit ((lisseYonedaFibreProduct.pr f y).op ⋙ H.obj))

/- 103.15.1.1 (2): Pushforward evaluation is global sections on the primed
Yoneda fibre product with its restricted projection. -/
@[stacks 07AU] #check (AlgebraicGeometry.AlgebraicStack.flatFppfPushforwardObjIsoGlobalSections :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Flat f]
    (H : Sheaf (flatFppfTopology X) (Type (u + 1))) (y : flatFppfSite Y)
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type (u + 1),
      (flatFppfMap f).op.HasPointwiseRightKanExtension P]
    [HasLimit ((flatYonedaFibreProduct.pr f y).op ⋙ H.obj)],
    (((flatFppfMap f).sheafPushforwardCocontinuous (Type (u + 1))
        (flatFppfTopology X) (flatFppfTopology Y)).obj H).obj.obj (op y) ≅
      limit ((flatYonedaFibreProduct.pr f y).op ⋙ H.obj))
