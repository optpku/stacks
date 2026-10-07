module

public import ReasLib.Algebra.Module.RelativeDualizing.Product
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

universe u

/- Lemma 49.2.7: for quasi-finite maps of Noetherian rings `A → B` and
`A → C`, the relative dualizing module of `B × C` over `A` is identified with
the product of the two relative dualizing modules. -/
@[stacks 0BT5] #check
  (Algebra.RelativeDualizingModule.prodComparisonOf_bijective :
    ∀ (A B' B C' C : Type u)
    [CommRing A] [CommRing B'] [CommRing B] [CommRing C'] [CommRing C]
    [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing C]
    [Algebra A B'] [Algebra B' B] [Algebra A B] [IsScalarTower A B' B]
    [Algebra A C'] [Algebra C' C] [Algebra A C] [IsScalarTower A C' C]
    (hB : Algebra.FiniteType.QuasiFinite A B)
    (hC : Algebra.FiniteType.QuasiFinite A C)
    [Module.Finite A B'] [Module.Finite A C']
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B' B)))]
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap C' C)))] ,
    Function.Bijective
      (Algebra.RelativeDualizingModule.prodComparisonOf A B' B C' C hB hC).hom)

/- The product comparison for chosen finite-open presentations is an isomorphism
of `B × C`-modules. -/
#check
  (Algebra.RelativeDualizingModule.prodComparisonOf_isIso :
    ∀ (A B' B C' C : Type u)
    [CommRing A] [CommRing B'] [CommRing B] [CommRing C'] [CommRing C]
    [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing C]
    [Algebra A B'] [Algebra B' B] [Algebra A B] [IsScalarTower A B' B]
    [Algebra A C'] [Algebra C' C] [Algebra A C] [IsScalarTower A C' C]
    (hB : Algebra.FiniteType.QuasiFinite A B)
    (hC : Algebra.FiniteType.QuasiFinite A C)
    [Module.Finite A B'] [Module.Finite A C']
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B' B)))]
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap C' C)))] ,
    CategoryTheory.IsIso
      (Algebra.RelativeDualizingModule.prodComparisonOf A B' B C' C hB hC))
