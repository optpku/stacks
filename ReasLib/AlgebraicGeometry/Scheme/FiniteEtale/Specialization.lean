/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.CategoryTheory.Galois.Topology
public import Mathlib.CategoryTheory.Galois.Action
public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale.FundamentalGroup
public import ReasLib.AlgebraicGeometry.Scheme.Henselization
public import ReasLib.AlgebraicGeometry.Scheme.Topology.Valuation

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.PreGaloisCategory
open AlgebraicGeometry

universe u w

namespace EtaleFundamentalGroup

/-- A continuous homomorphism on finite-étale fundamental groups is a specialization map
when it is induced by comparison through a strict henselization at the special point. -/
def IsSpecializationMap {X S : Scheme.{u}} (f : X ⟶ S)
    (sbar' sbar : Scheme.GeometricPoint S)
    (hSpec : Specializes sbar'.image sbar.image)
    (F' : Scheme.FiniteEtale (pullback f sbar'.hom) ⥤ FintypeCat.{w})
    (F : Scheme.FiniteEtale (pullback f sbar.hom) ⥤ FintypeCat.{w})
    [GaloisCategory (Scheme.FiniteEtale (pullback f sbar'.hom))]
    [FiberFunctor F']
    [GaloisCategory (Scheme.FiniteEtale (pullback f sbar.hom))]
    [FiberFunctor F]
    (sp : ContinuousMonoidHom (Aut F') (Aut F)) : Prop :=
  Specializes sbar'.image sbar.image ∧ ∃ (Rsh : Type u) (_ : CommRing Rsh)
      (_ : Algebra (S.presheaf.stalk sbar.image) Rsh)
      (_ : IsStrictHenselizationOf (S.presheaf.stalk sbar.image) Rsh),
    ∃ (generalLift : Spec (.of sbar'.K) ⟶ Scheme.strictHenselizationScheme S sbar Rsh)
      (specialLift : Spec (.of sbar.K) ⟶ Scheme.strictHenselizationScheme S sbar Rsh),
      generalLift ≫ Scheme.strictHenselizationMap S sbar Rsh = sbar'.hom ∧
        specialLift ≫ Scheme.strictHenselizationMap S sbar Rsh = sbar.hom ∧
        Specializes (generalLift default) (specialLift default) ∧
        ∃ (generalToStrict : pullback f sbar'.hom ⟶
              pullback f (Scheme.strictHenselizationMap S sbar Rsh))
          (specialToStrict : pullback f sbar.hom ⟶
              pullback f (Scheme.strictHenselizationMap S sbar Rsh)),
          generalToStrict ≫ pullback.fst f (Scheme.strictHenselizationMap S sbar Rsh) =
              pullback.fst f sbar'.hom ∧
            generalToStrict ≫ pullback.snd f (Scheme.strictHenselizationMap S sbar Rsh) =
              pullback.snd f sbar'.hom ≫ generalLift ∧
            specialToStrict ≫ pullback.fst f (Scheme.strictHenselizationMap S sbar Rsh) =
              pullback.fst f sbar.hom ∧
            specialToStrict ≫ pullback.snd f (Scheme.strictHenselizationMap S sbar Rsh) =
              pullback.snd f sbar.hom ≫ specialLift ∧
            ∃ (specialEquiv :
                  Scheme.FiniteEtale (pullback f (Scheme.strictHenselizationMap S sbar Rsh)) ≌
                    Scheme.FiniteEtale (pullback f sbar.hom)),
                specialEquiv.functor = Scheme.finiteEtaleBaseChange specialToStrict ∧
                ∃ _ :
                    CatCommSq (specialEquiv.inverse ⋙ Scheme.finiteEtaleBaseChange generalToStrict)
                      (functorToAction F) (functorToAction F')
                      (Action.res FintypeCat sp.toMonoidHom),
                  exactFunctor (Scheme.FiniteEtale (pullback f sbar.hom))
                    (Scheme.FiniteEtale (pullback f sbar'.hom))
                    (specialEquiv.inverse ⋙ Scheme.finiteEtaleBaseChange generalToStrict)

/-- A specialization map is equivalently specified by strict-henselization lifts,
the special-fiber base-change equivalence, general-fiber restriction, and the
compatible exact action comparison. -/
theorem IsSpecializationMap.iff_exists {X S : Scheme.{u}} (f : X ⟶ S)
    (sbar' sbar : Scheme.GeometricPoint S)
    (hSpec : Specializes sbar'.image sbar.image)
    (F' : Scheme.FiniteEtale (pullback f sbar'.hom) ⥤ FintypeCat.{w})
    (F : Scheme.FiniteEtale (pullback f sbar.hom) ⥤ FintypeCat.{w})
    [GaloisCategory (Scheme.FiniteEtale (pullback f sbar'.hom))]
    [FiberFunctor F']
    [GaloisCategory (Scheme.FiniteEtale (pullback f sbar.hom))]
    [FiberFunctor F]
    (sp : ContinuousMonoidHom (Aut F') (Aut F)) :
    IsSpecializationMap f sbar' sbar hSpec F' F sp ↔
      Specializes sbar'.image sbar.image ∧ ∃ (Rsh : Type u) (_ : CommRing Rsh)
          (_ : Algebra (S.presheaf.stalk sbar.image) Rsh)
          (_ : IsStrictHenselizationOf (S.presheaf.stalk sbar.image) Rsh),
        ∃ (generalLift : Spec (.of sbar'.K) ⟶ Scheme.strictHenselizationScheme S sbar Rsh)
          (specialLift : Spec (.of sbar.K) ⟶ Scheme.strictHenselizationScheme S sbar Rsh),
          generalLift ≫ Scheme.strictHenselizationMap S sbar Rsh = sbar'.hom ∧
            specialLift ≫ Scheme.strictHenselizationMap S sbar Rsh = sbar.hom ∧
            Specializes (generalLift default) (specialLift default) ∧
            ∃ (generalToStrict : pullback f sbar'.hom ⟶
                  pullback f (Scheme.strictHenselizationMap S sbar Rsh))
              (specialToStrict : pullback f sbar.hom ⟶
                  pullback f (Scheme.strictHenselizationMap S sbar Rsh)),
              generalToStrict ≫ pullback.fst f (Scheme.strictHenselizationMap S sbar Rsh) =
                  pullback.fst f sbar'.hom ∧
                generalToStrict ≫ pullback.snd f (Scheme.strictHenselizationMap S sbar Rsh) =
                  pullback.snd f sbar'.hom ≫ generalLift ∧
                specialToStrict ≫ pullback.fst f (Scheme.strictHenselizationMap S sbar Rsh) =
                  pullback.fst f sbar.hom ∧
                specialToStrict ≫ pullback.snd f (Scheme.strictHenselizationMap S sbar Rsh) =
                  pullback.snd f sbar.hom ≫ specialLift ∧
                ∃ (specialEquiv :
                      Scheme.FiniteEtale (pullback f (Scheme.strictHenselizationMap S sbar Rsh)) ≌
                        Scheme.FiniteEtale (pullback f sbar.hom)),
                    specialEquiv.functor = Scheme.finiteEtaleBaseChange specialToStrict ∧
                    ∃ _ :
                        CatCommSq (specialEquiv.inverse ⋙ Scheme.finiteEtaleBaseChange generalToStrict)
                          (functorToAction F) (functorToAction F')
                          (Action.res FintypeCat sp.toMonoidHom),
                      exactFunctor (Scheme.FiniteEtale (pullback f sbar.hom))
                        (Scheme.FiniteEtale (pullback f sbar'.hom))
                        (specialEquiv.inverse ⋙ Scheme.finiteEtaleBaseChange generalToStrict) := sorry

/-- A specialization map records that the underlying points of `sbar'` and `sbar` specialize. -/
theorem IsSpecializationMap.specializes {X S : Scheme.{u}} (f : X ⟶ S)
    (sbar' sbar : Scheme.GeometricPoint S)
    (hSpec : Specializes sbar'.image sbar.image)
    (F' : Scheme.FiniteEtale (pullback f sbar'.hom) ⥤ FintypeCat.{w})
    (F : Scheme.FiniteEtale (pullback f sbar.hom) ⥤ FintypeCat.{w})
    [GaloisCategory (Scheme.FiniteEtale (pullback f sbar'.hom))]
    [FiberFunctor F']
    [GaloisCategory (Scheme.FiniteEtale (pullback f sbar.hom))]
    [FiberFunctor F]
    (sp : ContinuousMonoidHom (Aut F') (Aut F))
    (hsp : IsSpecializationMap f sbar' sbar hSpec F' F sp) :
    Specializes sbar'.image sbar.image := sorry

namespace IsSpecializationMap

/-- Composition of specialization maps is again a specialization map along the
composite specialization of geometric points. -/
theorem comp {X S : Scheme.{u}} (f : X ⟶ S)
    [IsProper f] [GeometricallyConnected f]
    (sbar'' sbar' sbar : Scheme.GeometricPoint S)
    (hSpec₁ : Specializes sbar''.image sbar'.image)
    (hSpec₂ : Specializes sbar'.image sbar.image)
    (F'' : Scheme.FiniteEtale (pullback f sbar''.hom) ⥤ FintypeCat.{w})
    (F' : Scheme.FiniteEtale (pullback f sbar'.hom) ⥤ FintypeCat.{w})
    (F : Scheme.FiniteEtale (pullback f sbar.hom) ⥤ FintypeCat.{w})
    [GaloisCategory (Scheme.FiniteEtale (pullback f sbar''.hom))]
    [FiberFunctor F'']
    [GaloisCategory (Scheme.FiniteEtale (pullback f sbar'.hom))]
    [FiberFunctor F']
    [GaloisCategory (Scheme.FiniteEtale (pullback f sbar.hom))]
    [FiberFunctor F]
    (sp₁ : ContinuousMonoidHom (Aut F'') (Aut F'))
    (hsp₁ : IsSpecializationMap f sbar'' sbar' hSpec₁ F'' F' sp₁)
    (sp₂ : ContinuousMonoidHom (Aut F') (Aut F))
    (hsp₂ : IsSpecializationMap f sbar' sbar hSpec₂ F' F sp₂) :
    IsSpecializationMap f sbar'' sbar (hSpec₁.trans hSpec₂) F'' F (sp₂.comp sp₁) := sorry

/-- A continuous homomorphism is the specialization map induced by a valuative realization when
the finite-étale comparison is taken through `Spec D.V → S` rather than through an unrelated
strict henselization. -/
def inducedByValuation {X S : Scheme.{u}} (f : X ⟶ S)
    (sbar' sbar : Scheme.GeometricPoint S)
    (hSpec : Specializes sbar'.image sbar.image)
    (F' : Scheme.FiniteEtale (pullback f sbar'.hom) ⥤ FintypeCat.{w})
    (F : Scheme.FiniteEtale (pullback f sbar.hom) ⥤ FintypeCat.{w})
    [GaloisCategory (Scheme.FiniteEtale (pullback f sbar'.hom))]
    [FiberFunctor F']
    [GaloisCategory (Scheme.FiniteEtale (pullback f sbar.hom))]
    [FiberFunctor F]
    (D : _root_.Specializes.ValuationRealization sbar'.toFieldValuedPoint.image
      sbar.toFieldValuedPoint.image (sbar'.toFieldValuedPoint.residueFieldHom))
    (sp_R : ContinuousMonoidHom (Aut F') (Aut F)) : Prop :=
  ∃ (generalLift : Spec (.of sbar'.K) ⟶ Spec (CommRingCat.of D.V))
    (specialLift : Spec (.of sbar.K) ⟶ Spec (CommRingCat.of D.V)),
    generalLift ≫ D.hom = sbar'.hom ∧
      specialLift ≫ D.hom = sbar.hom ∧
      Specializes (generalLift default) (specialLift default) ∧
      ∃ (generalToVal : pullback f sbar'.hom ⟶ pullback f D.hom)
        (specialToVal : pullback f sbar.hom ⟶ pullback f D.hom),
        generalToVal ≫ pullback.fst f D.hom = pullback.fst f sbar'.hom ∧
          generalToVal ≫ pullback.snd f D.hom = pullback.snd f sbar'.hom ≫ generalLift ∧
          specialToVal ≫ pullback.fst f D.hom = pullback.fst f sbar.hom ∧
          specialToVal ≫ pullback.snd f D.hom = pullback.snd f sbar.hom ≫ specialLift ∧
          ∃ (specialEquiv :
                Scheme.FiniteEtale (pullback f D.hom) ≌
                  Scheme.FiniteEtale (pullback f sbar.hom)),
              specialEquiv.functor = Scheme.finiteEtaleBaseChange specialToVal ∧
              ∃ _ :
                  CatCommSq (specialEquiv.inverse ⋙ Scheme.finiteEtaleBaseChange generalToVal)
                    (functorToAction F) (functorToAction F')
                    (Action.res FintypeCat sp_R.toMonoidHom),
                exactFunctor (Scheme.FiniteEtale (pullback f sbar.hom))
                  (Scheme.FiniteEtale (pullback f sbar'.hom))
                  (specialEquiv.inverse ⋙ Scheme.finiteEtaleBaseChange generalToVal)

/-- The defining comparison through `Spec D.V` of `inducedByValuation`. -/
theorem inducedByValuation_spec {X S : Scheme.{u}} (f : X ⟶ S)
    (sbar' sbar : Scheme.GeometricPoint S)
    (hSpec : Specializes sbar'.image sbar.image)
    (F' : Scheme.FiniteEtale (pullback f sbar'.hom) ⥤ FintypeCat.{w})
    (F : Scheme.FiniteEtale (pullback f sbar.hom) ⥤ FintypeCat.{w})
    [GaloisCategory (Scheme.FiniteEtale (pullback f sbar'.hom))]
    [FiberFunctor F']
    [GaloisCategory (Scheme.FiniteEtale (pullback f sbar.hom))]
    [FiberFunctor F]
    (D : _root_.Specializes.ValuationRealization sbar'.toFieldValuedPoint.image
      sbar.toFieldValuedPoint.image (sbar'.toFieldValuedPoint.residueFieldHom))
    (sp_R : ContinuousMonoidHom (Aut F') (Aut F)) :
    inducedByValuation f sbar' sbar hSpec F' F D sp_R ↔
      ∃ (generalLift : Spec (.of sbar'.K) ⟶ Spec (CommRingCat.of D.V))
        (specialLift : Spec (.of sbar.K) ⟶ Spec (CommRingCat.of D.V)),
        generalLift ≫ D.hom = sbar'.hom ∧
          specialLift ≫ D.hom = sbar.hom ∧
          Specializes (generalLift default) (specialLift default) ∧
          ∃ (generalToVal : pullback f sbar'.hom ⟶ pullback f D.hom)
            (specialToVal : pullback f sbar.hom ⟶ pullback f D.hom),
            generalToVal ≫ pullback.fst f D.hom = pullback.fst f sbar'.hom ∧
              generalToVal ≫ pullback.snd f D.hom = pullback.snd f sbar'.hom ≫ generalLift ∧
              specialToVal ≫ pullback.fst f D.hom = pullback.fst f sbar.hom ∧
              specialToVal ≫ pullback.snd f D.hom = pullback.snd f sbar.hom ≫ specialLift ∧
              ∃ (specialEquiv :
                    Scheme.FiniteEtale (pullback f D.hom) ≌
                      Scheme.FiniteEtale (pullback f sbar.hom)),
                  specialEquiv.functor = Scheme.finiteEtaleBaseChange specialToVal ∧
                  ∃ _ :
                      CatCommSq (specialEquiv.inverse ⋙ Scheme.finiteEtaleBaseChange generalToVal)
                        (functorToAction F) (functorToAction F')
                        (Action.res FintypeCat sp_R.toMonoidHom),
                    exactFunctor (Scheme.FiniteEtale (pullback f sbar.hom))
                      (Scheme.FiniteEtale (pullback f sbar'.hom))
                      (specialEquiv.inverse ⋙ Scheme.finiteEtaleBaseChange generalToVal) := sorry

/-- The given specialization map is isomorphic to the map induced by a strictly henselian
valuation ring over `S` that dominates the image of a strict henselization of `O_{S,s}` used
to construct the original map. -/
def valuationInduced {X S : Scheme.{u}} (f : X ⟶ S)
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
    (D : _root_.Specializes.ValuationRealization sbar'.toFieldValuedPoint.image
      sbar.toFieldValuedPoint.image (sbar'.toFieldValuedPoint.residueFieldHom))
    (Rsh : Type u) [CommRing Rsh]
    [Algebra (S.presheaf.stalk sbar.image) Rsh]
    [IsStrictHenselizationOf (S.presheaf.stalk sbar.image) Rsh]
    (strictToField : Rsh →+* sbar'.toFieldValuedPoint.K)
    (e' : Aut F' ≃* Aut F') (e : Aut F ≃* Aut F) : Prop :=
  StrictHenselianLocalRing D.V ∧
    IsAlgClosed (FractionRing D.V) ∧
      (strictToField.comp (algebraMap (S.presheaf.stalk sbar.image) Rsh)).range ≤ D.V.toSubring ∧
      ∃ (sp_R : ContinuousMonoidHom (Aut F') (Aut F)),
        inducedByValuation f sbar' sbar hSpec F' F D sp_R ∧
          e.toMonoidHom.comp sp.toMonoidHom = sp_R.toMonoidHom.comp e'.toMonoidHom

/-- The defining strict-henselian, domination, induced-map, and conjugacy data of
`valuationInduced`. -/
theorem valuationInduced_spec {X S : Scheme.{u}} (f : X ⟶ S)
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
    (D : _root_.Specializes.ValuationRealization sbar'.toFieldValuedPoint.image
      sbar.toFieldValuedPoint.image (sbar'.toFieldValuedPoint.residueFieldHom))
    (Rsh : Type u) [CommRing Rsh]
    [Algebra (S.presheaf.stalk sbar.image) Rsh]
    [IsStrictHenselizationOf (S.presheaf.stalk sbar.image) Rsh]
    (strictToField : Rsh →+* sbar'.toFieldValuedPoint.K)
    (e' : Aut F' ≃* Aut F') (e : Aut F ≃* Aut F) :
    valuationInduced f sbar' sbar hSpec F' F sp hsp D Rsh strictToField e' e ↔
      StrictHenselianLocalRing D.V ∧
        IsAlgClosed (FractionRing D.V) ∧
          (strictToField.comp
            (algebraMap (S.presheaf.stalk sbar.image) Rsh)).range ≤ D.V.toSubring ∧
          ∃ (sp_R : ContinuousMonoidHom (Aut F') (Aut F)),
            inducedByValuation f sbar' sbar hSpec F' F D sp_R ∧
              e.toMonoidHom.comp sp.toMonoidHom =
                sp_R.toMonoidHom.comp e'.toMonoidHom := sorry

/-- For a proper morphism with geometrically connected fibres, every
specialization map along `sbar' ⤳ sbar` is isomorphic to the specialization map induced
by a strictly henselian valuation ring over `S` with algebraically closed fraction field. -/
theorem exists_strictHenselianValuationRing {X S : Scheme.{u}} (f : X ⟶ S)
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
    (hsp : IsSpecializationMap f sbar' sbar hSpec F' F sp) :
    ∃ (D : _root_.Specializes.ValuationRealization sbar'.toFieldValuedPoint.image
        sbar.toFieldValuedPoint.image (sbar'.toFieldValuedPoint.residueFieldHom))
      (Rsh : Type u) (_ : CommRing Rsh)
      (_ : Algebra (S.presheaf.stalk sbar.image) Rsh)
      (_ : IsStrictHenselizationOf (S.presheaf.stalk sbar.image) Rsh)
      (strictToField : Rsh →+* sbar'.toFieldValuedPoint.K)
      (e' : Aut F' ≃* Aut F') (e : Aut F ≃* Aut F),
      valuationInduced f sbar' sbar hSpec F' F sp hsp D Rsh strictToField e' e := sorry

end IsSpecializationMap

end EtaleFundamentalGroup
