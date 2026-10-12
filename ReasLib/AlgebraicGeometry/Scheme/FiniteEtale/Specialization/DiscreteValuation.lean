/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale.Specialization
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.AlgebraicGeometry.Noetherian

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.PreGaloisCategory
open AlgebraicGeometry

universe u w

namespace EtaleFundamentalGroup.IsSpecializationMap

/-- A homomorphism of geometric fundamental groups is induced by a strictly henselian
discrete valuation ring over the base when compatible geometric field extensions identify
its exact specialization functor with special-fibre restriction followed by generic-fibre
base change. -/
def dvrInduced {X S : Scheme.{u}} (f : X ⟶ S)
    (sbar' sbar : Scheme.GeometricPoint S)
    (F' : Scheme.FiniteEtale (pullback f sbar'.hom) ⥤ FintypeCat.{w})
    (F : Scheme.FiniteEtale (pullback f sbar.hom) ⥤ FintypeCat.{w})
    [GaloisCategory (Scheme.FiniteEtale (pullback f sbar'.hom))]
    [FiberFunctor F']
    [GaloisCategory (Scheme.FiniteEtale (pullback f sbar.hom))]
    [FiberFunctor F]
    (sp : ContinuousMonoidHom (Aut F') (Aut F))
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [StrictHenselianLocalRing R] (k : Spec (CommRingCat.of R) ⟶ S) : Prop :=
  ∃ (etaBar closedBar : Scheme.GeometricPoint (Spec (CommRingCat.of R))),
    etaBar.image = genericPoint (Spec (CommRingCat.of R)) ∧
      closedBar.image = IsLocalRing.closedPoint R ∧
      ∃ (generalComparison : Spec (.of etaBar.K) ⟶ Spec (.of sbar'.K))
        (specialComparison : Spec (.of closedBar.K) ⟶ Spec (.of sbar.K))
        (hGeneral : etaBar.hom ≫ k = generalComparison ≫ sbar'.hom)
        (hSpecial : closedBar.hom ≫ k = specialComparison ≫ sbar.hom),
        let fR := pullback.snd f k
        let generalFiberMap := pullback.map fR etaBar.hom f sbar'.hom
          (pullback.fst f k) generalComparison k pullback.condition.symm hGeneral
        let specialFiberMap := pullback.map fR closedBar.hom f sbar.hom
          (pullback.fst f k) specialComparison k pullback.condition.symm hSpecial
        ∃ (generalEquiv : Scheme.FiniteEtale (pullback f sbar'.hom) ≌
              Scheme.FiniteEtale (pullback fR etaBar.hom))
          (specialFieldEquiv : Scheme.FiniteEtale (pullback f sbar.hom) ≌
              Scheme.FiniteEtale (pullback fR closedBar.hom)),
          generalEquiv.functor = Scheme.finiteEtaleBaseChange generalFiberMap ∧
            specialFieldEquiv.functor = Scheme.finiteEtaleBaseChange specialFiberMap ∧
            ∃ (specialEquiv : Scheme.FiniteEtale (pullback f k) ≌
                Scheme.FiniteEtale (pullback fR closedBar.hom)),
              specialEquiv.functor =
                  Scheme.finiteEtaleBaseChange (pullback.fst fR closedBar.hom) ∧
                let specializationFunctor := specialFieldEquiv.functor ⋙ specialEquiv.inverse ⋙
                  Scheme.finiteEtaleBaseChange (pullback.fst fR etaBar.hom) ⋙ generalEquiv.inverse
                ∃ _ : CatCommSq specializationFunctor (functorToAction F) (functorToAction F')
                    (Action.res FintypeCat sp.toMonoidHom),
                  exactFunctor (Scheme.FiniteEtale (pullback f sbar.hom))
                    (Scheme.FiniteEtale (pullback f sbar'.hom)) specializationFunctor

/-- For a proper morphism with geometrically connected fibres over a Noetherian scheme,
every specialization map is induced, up to compatible geometric field-extension
comparisons, by a strictly henselian discrete valuation ring over the base. -/
theorem exists_strictHenselianDvr {X S : Scheme.{u}} (f : X ⟶ S)
    [IsProper f] [GeometricallyConnected f]
    (sbar' sbar : Scheme.GeometricPoint S)
    (hSpec : Specializes sbar'.image sbar.image)
    (F' : Scheme.FiniteEtale (pullback f sbar'.hom) ⥤ FintypeCat.{w})
    (F : Scheme.FiniteEtale (pullback f sbar.hom) ⥤ FintypeCat.{w})
    [GaloisCategory (Scheme.FiniteEtale (pullback f sbar'.hom))]
    [FiberFunctor F']
    [GaloisCategory (Scheme.FiniteEtale (pullback f sbar.hom))]
    [FiberFunctor F]
    (sp : ContinuousMonoidHom (Aut F') (Aut F))
    (hsp : IsSpecializationMap f sbar' sbar hSpec F' F sp)
    [IsNoetherian S] :
    ∃ (R : Type u) (_ : CommRing R) (_ : IsDomain R)
      (_ : IsDiscreteValuationRing R) (_ : StrictHenselianLocalRing R)
      (k : Spec (CommRingCat.of R) ⟶ S),
      dvrInduced f sbar' sbar F' F sp R k := sorry

end EtaleFundamentalGroup.IsSpecializationMap
