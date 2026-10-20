module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Representable.OnSpace
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

/- 94.9.8.1: let `F` and `G` be algebraic spaces over `S` representing the
2-fibre product `TwoFibreProduct.apex g f` and the base `Z`. The 1-morphism
`TwoFibreProduct.fst g f` corresponds to a morphism `f' : F ⟶ G` of algebraic
spaces. The right square is the 2-fibre product, with projections
`TwoFibreProduct.fst`, `TwoFibreProduct.snd` and 2-commutativity
`TwoFibreProduct.comparisonIso`. Squiggly arrows are the associated sheaf of
isomorphism classes of a category fibred in setoids, equivalently a representing
equivalence with `AlgebraicSpace.toGroupoids` (compared after `uliftFunctor`
with `Functor.fiberIsoClassPresheaf`). -/
@[stacks 0403]
#check (AlgebraicGeometry.RepresentsTwoFibreProductOnSpace.exists_morphism :
  ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    (f : X ⟶ Y) (g : Z ⟶ Y) (F G : AlgebraicSpace S)
    (eZ : Z ≌ G.toGroupoids)
    (eApex : TwoFibreProduct.apex.{u + 1, u, u + 1, u} g f ≌ F.toGroupoids),
    ∃ f' : F ⟶ G,
      Nonempty
        (eApex.hom ≫ AlgebraicSpace.toGroupoids.map f' ≅
          TwoFibreProduct.fst.{u + 1, u, u + 1, u} g f ≫ eZ.hom) ∧
      ∃ (iZ : Functor.fiberIsoClassPresheaf Z.p ≅
          G.functorOfPoints ⋙ uliftFunctor.{u + 1, u})
        (iApex : Functor.fiberIsoClassPresheaf
            (FiberedCategoryOver.Groupoids.p
              (TwoFibreProduct.apex.{u + 1, u, u + 1, u} g f)) ≅
          F.functorOfPoints ⋙ uliftFunctor.{u + 1, u}),
        BasedFunctor.fiberIsoClassMap
            (FiberedCategoryOver.Groupoids.toBasedFunctor
              (TwoFibreProduct.fst.{u + 1, u, u + 1, u} g f)) =
          iApex.hom ≫ Functor.whiskerRight f' uliftFunctor.{u + 1, u} ≫ iZ.inv)
