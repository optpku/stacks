module

public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale.Specialization.Naturality
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.PreGaloisCategory
open AlgebraicGeometry

universe u w

/- Lemma 58.16.1: specialization maps for proper families with geometrically connected
fibers are natural with respect to a commutative square of schemes. -/
@[stacks 0C0K] #check (EtaleFundamentalGroup.IsSpecializationMap.naturality :
    ∀ {Y X T S : Scheme.{u}} (i : Y ⟶ X) (g : Y ⟶ T)
    (f : X ⟶ S) (k : T ⟶ S) (sq : CommSq i g f k)
    [IsProper f] [GeometricallyConnected f]
    [IsProper g] [GeometricallyConnected g]
    (tbar' tbar : Scheme.GeometricPoint T)
    (hSpec : Specializes tbar'.image tbar.image)
    (FY' : Scheme.FiniteEtale (pullback g tbar'.hom) ⥤ FintypeCat.{w})
    (FY : Scheme.FiniteEtale (pullback g tbar.hom) ⥤ FintypeCat.{w})
    (FX' : Scheme.FiniteEtale (pullback f (tbar'.map k).hom) ⥤ FintypeCat.{w})
    (FX : Scheme.FiniteEtale (pullback f (tbar.map k).hom) ⥤ FintypeCat.{w})
    [GaloisCategory (Scheme.FiniteEtale (pullback g tbar'.hom))]
    [FiberFunctor FY']
    [GaloisCategory (Scheme.FiniteEtale (pullback g tbar.hom))]
    [FiberFunctor FY]
    [GaloisCategory (Scheme.FiniteEtale (pullback f (tbar'.map k).hom))]
    [FiberFunctor FX']
    [GaloisCategory (Scheme.FiniteEtale (pullback f (tbar.map k).hom))]
    [FiberFunctor FX]
    (spY : ContinuousMonoidHom (Aut FY') (Aut FY))
    (hspY : EtaleFundamentalGroup.IsSpecializationMap
      g tbar' tbar hSpec FY' FY spY),
    ∃ (left : ContinuousMonoidHom (Aut FY') (Aut FX'))
      (right : ContinuousMonoidHom (Aut FY) (Aut FX))
      (spX : ContinuousMonoidHom (Aut FX') (Aut FX))
      (leftSquare : CatCommSq
          (Scheme.finiteEtaleBaseChange
            (Scheme.Hom.geometricFiberMap i g f k sq tbar'))
          (functorToAction FX') (functorToAction FY')
          (Action.res FintypeCat left.toMonoidHom))
      (rightSquare : CatCommSq
          (Scheme.finiteEtaleBaseChange
            (Scheme.Hom.geometricFiberMap i g f k sq tbar))
          (functorToAction FX) (functorToAction FY)
          (Action.res FintypeCat right.toMonoidHom)),
      EtaleFundamentalGroup.IsSpecializationMap f
          (tbar'.map k) (tbar.map k)
          (Scheme.GeometricPoint.map_specializes hSpec k) FX' FX spX ∧
        CommSq (ProfiniteGrp.ofHom spY) (ProfiniteGrp.ofHom left)
          (ProfiniteGrp.ofHom right) (ProfiniteGrp.ofHom spX))
