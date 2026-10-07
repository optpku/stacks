module

import StacksCheckRecall
public import stacks_project.Chap48.Lemma_48_20_6_FiniteTypeOver
public import stacks_project.Chap48.Lemma_48_20_6_NormalizedRelative

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 48.20.6: if `ωX` and `ωY` are dualizing complexes normalized relative to the
same dualizing complex `ωS`, then along an `S`-morphism `f : X ⟶ Y` between schemes of finite
type over `S`, the complex `ωX` is normalized relative to `ωY`. -/
@[stacks 0AUB] #check
  (AlgebraicGeometry.Scheme.Hom.NormalizedDualizingComplex.RelativeTo.trans :
    ∀ {S : Scheme.{u}} [IsNoetherian S]
      {X Y : Scheme.FiniteTypeOver S} (f : X ⟶ Y),
      let X' : Scheme := X.obj.left
      let Y' : Scheme := Y.obj.left
      let f' : X' ⟶ Y' := f.hom.left
      ∀ [MonoidalCategory (RingedSpace.ModuleDerived S.toRingedSpace)]
        (HS : MonoidalClosed (RingedSpace.ModuleDerived S.toRingedSpace))
        [MonoidalCategory (RingedSpace.ModuleDerived X'.toRingedSpace)]
        (HX : MonoidalClosed (RingedSpace.ModuleDerived X'.toRingedSpace))
        [MonoidalCategory (RingedSpace.ModuleDerived Y'.toRingedSpace)]
        (HY : MonoidalClosed (RingedSpace.ModuleDerived Y'.toRingedSpace))
        (ωS : RingedSpace.ModuleDerived S.toRingedSpace) (hωS : ωS.IsDualizingComplex HS)
        (ωX : RingedSpace.ModuleDerived X'.toRingedSpace)
        (ωY : RingedSpace.ModuleDerived Y'.toRingedSpace)
        (hX : @AlgebraicGeometry.Scheme.Hom.NormalizedDualizingComplex.RelativeTo _ _ _
          X.obj.hom (AlgebraicGeometry.Scheme.FiniteTypeOver.instFiniteType X) _ HS _ HX
          ωS hωS ωX)
        (hY : @AlgebraicGeometry.Scheme.Hom.NormalizedDualizingComplex.RelativeTo _ _ _
          Y.obj.hom (AlgebraicGeometry.Scheme.FiniteTypeOver.instFiniteType Y) _ HS _ HY
          ωS hωS ωY),
        @AlgebraicGeometry.Scheme.Hom.NormalizedDualizingComplex.RelativeTo _ _ _ f'
          (AlgebraicGeometry.Scheme.FiniteTypeOver.instFiniteTypeHom f) _ HY _ HX ωY
          (@AlgebraicGeometry.Scheme.Hom.NormalizedDualizingComplex.RelativeTo.isDualizing
            _ _ _ Y.obj.hom (AlgebraicGeometry.Scheme.FiniteTypeOver.instFiniteType Y) _ HS _
            HY ωS hωS ωY hY : ωY.IsDualizingComplex HY) ωX)
