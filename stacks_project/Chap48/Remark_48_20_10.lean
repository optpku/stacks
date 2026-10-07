module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Dualizing.NewUpperShriek

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped DerivedCategory.CohomologyIn

universe u

/- Remark 48.20.10: for a finite-type morphism `f : X ⟶ Y` between schemes of finite
type over a Noetherian scheme `S`, the functor `NewUpperShriek.functor f` is independent,
up to canonical isomorphism, of the dualizing complex on `S` and of the dualizing complexes
on `X` and `Y` normalized relative to it. -/
@[stacks 0BV3] #check
  (AlgebraicGeometry.Scheme.Hom.NewUpperShriek.functor_isIsomorphic :
    ∀ {S : Scheme.{u}} [IsNoetherian S] {X Y : Scheme.FiniteTypeOver S} (f : X ⟶ Y),
    let X' : Scheme := X.obj.left
    let Y' : Scheme := Y.obj.left
    let f' : X' ⟶ Y' := f.hom.left
    ∀ [MonoidalCategory (RingedSpace.ModuleDerived S.toRingedSpace)]
      [BraidedCategory (RingedSpace.ModuleDerived S.toRingedSpace)]
      (HS : MonoidalClosed (RingedSpace.ModuleDerived S.toRingedSpace))
      [MonoidalCategory (RingedSpace.ModuleDerived X'.toRingedSpace)]
      [BraidedCategory (RingedSpace.ModuleDerived X'.toRingedSpace)]
      (HX : MonoidalClosed (RingedSpace.ModuleDerived X'.toRingedSpace))
      [MonoidalCategory (RingedSpace.ModuleDerived Y'.toRingedSpace)]
      [BraidedCategory (RingedSpace.ModuleDerived Y'.toRingedSpace)]
      (HY : MonoidalClosed (RingedSpace.ModuleDerived Y'.toRingedSpace))
      (ωS ωS' : RingedSpace.ModuleDerived S.toRingedSpace)
      (hωS : ωS.IsDualizingComplex HS) (hωS' : ωS'.IsDualizingComplex HS)
      (ωX ωX' : RingedSpace.ModuleDerived X'.toRingedSpace)
      (ωY ωY' : RingedSpace.ModuleDerived Y'.toRingedSpace)
      (hX : @Scheme.Hom.NormalizedDualizingComplex.RelativeTo _ _ _ X.obj.hom
        (Scheme.FiniteTypeOver.instFiniteType X) _ HS _ HX ωS hωS ωX)
      (hX' : @Scheme.Hom.NormalizedDualizingComplex.RelativeTo _ _ _ X.obj.hom
        (Scheme.FiniteTypeOver.instFiniteType X) _ HS _ HX ωS' hωS' ωX')
      (hY : @Scheme.Hom.NormalizedDualizingComplex.RelativeTo _ _ _ Y.obj.hom
        (Scheme.FiniteTypeOver.instFiniteType Y) _ HS _ HY ωS hωS ωY)
      (hY' : @Scheme.Hom.NormalizedDualizingComplex.RelativeTo _ _ _ Y.obj.hom
        (Scheme.FiniteTypeOver.instFiniteType Y) _ HS _ HY ωS' hωS' ωY'),
      IsIsomorphic
        (@Scheme.Hom.NewUpperShriek.functor _ _ f'
          (Scheme.FiniteTypeOver.instFiniteTypeHom f) _ _ HX _ _ HY ωX ωY
          (@Scheme.Hom.NormalizedDualizingComplex.RelativeTo.isDualizing _ _ _ X.obj.hom
            (Scheme.FiniteTypeOver.instFiniteType X) _ HS _ HX ωS hωS ωX hX)
          (@Scheme.Hom.NormalizedDualizingComplex.RelativeTo.isDualizing _ _ _ Y.obj.hom
            (Scheme.FiniteTypeOver.instFiniteType Y) _ HS _ HY ωS hωS ωY hY))
        (@Scheme.Hom.NewUpperShriek.functor _ _ f'
          (Scheme.FiniteTypeOver.instFiniteTypeHom f) _ _ HX _ _ HY ωX' ωY'
          (@Scheme.Hom.NormalizedDualizingComplex.RelativeTo.isDualizing _ _ _ X.obj.hom
            (Scheme.FiniteTypeOver.instFiniteType X) _ HS _ HX ωS' hωS' ωX' hX')
          (@Scheme.Hom.NormalizedDualizingComplex.RelativeTo.isDualizing _ _ _ Y.obj.hom
            (Scheme.FiniteTypeOver.instFiniteType Y) _ HS _ HY ωS' hωS' ωY' hY')))
