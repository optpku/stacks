/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.DeligneSystem.ExtensionByZero
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.DeligneSystem.Comparison
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pullback.Composition

/-!
# Restriction maps between Deligne extensions

This module constructs and characterizes the canonical morphisms between compactly supported
Deligne extensions associated to nested open immersions.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Functor
open DerivedCategory.Bounded.CohomologyIn
open DerivedCategory.TStructure
open scoped DerivedCategory.CohomologyIn

noncomputable section

universe v


namespace AlgebraicGeometry.Scheme.Modules.IdealPowerComplex

variable {X : Scheme.{v}}

/-- Inclusion of ideal sheaves induces factorization of every ideal-power filtration stage. -/
theorem filtrationStage_factors {I I' : X.IdealSheafData} (h : I' ≤ I)
    (M : X.Modules) (q : ℤ) :
    ((IdealPowerFiltration.filtration I M).stage q).Factors
      ((IdealPowerFiltration.filtration I' M).stage q).arrow := sorry

/-- The filtration-preserving identity map induced by an inclusion of ideal sheaves. -/
noncomputable def filteredHom {I I' : X.IdealSheafData} (h : I' ≤ I)
    (M : X.Modules) :
    (IdealPowerFiltration.filtered I').obj M ⟶
      (IdealPowerFiltration.filtered I).obj M where
  hom := 𝟙 M
  preserves q := filtrationStage_factors h M q

/-- The identity maps on the terms of a complex respect the two ideal-power filtrations. -/
theorem filteredComplexHom_comm {I I' : X.IdealSheafData} (h : I' ≤ I)
    (F : CochainComplex X.Modules ℤ) (p q : ℤ) (hpq : (ComplexShape.up ℤ).Rel p q) :
    filteredHom h (F.X p) ≫ (filtered I F).d p q =
      (filtered I' F).d p q ≫ filteredHom h (F.X q) := sorry

/-- The filtered-complex morphism induced by the inclusions `(I') ^ n F ⊆ I ^ n F`. -/
noncomputable def filteredComplexHom {I I' : X.IdealSheafData} (h : I' ≤ I)
    (F : CochainComplex X.Modules ℤ) :
    filtered I' F ⟶ filtered I F where
  f p := filteredHom h (F.X p)
  comm' p q hpq := filteredComplexHom_comm h F p q hpq

/-- The morphism from the `(I') ^ n F` stage to the `I ^ n F` stage induced by `I' ≤ I`. -/
noncomputable def stageInclusion {I I' : X.IdealSheafData} (h : I' ≤ I)
    (F : CochainComplex X.Modules ℤ) (n : ℕ) :
    HomologicalComplex.Filtered.Stage.complex (filtered I' F) (n : ℤ) ⟶
      HomologicalComplex.Filtered.Stage.complex (filtered I F) (n : ℤ) :=
  HomologicalComplex.Filtered.Stage.map (filteredComplexHom h F) (n : ℤ)

/-- In every cochain degree, the stage morphism induced by `I' ≤ I` is the canonical
inclusion of the corresponding ideal-power subobjects. -/
theorem stageInclusion_f_comp_arrow {I I' : X.IdealSheafData} (h : I' ≤ I)
    (F : CochainComplex X.Modules ℤ) (n : ℕ) (q : ℤ) :
    (stageInclusion h F n).f q ≫
        ((IdealPowerFiltration.filtration I (F.X q)).stage (n : ℤ)).arrow =
      ((IdealPowerFiltration.filtration I' (F.X q)).stage (n : ℤ)).arrow := sorry

/-- The localized stage inclusions commute with the transition maps of the two positive
ideal-power systems. -/
theorem systemInclusion_naturality {I I' : X.IdealSheafData} (h : I' ≤ I)
    (F : CochainComplex X.Modules ℤ) {m n : OrderDual ℕ+} (f : m ⟶ n) :
    (positiveDerivedSystem I' F).map f ≫
        DerivedCategory.Q.map (stageInclusion h F ((OrderDual.ofDual n : ℕ+) : ℕ)) =
      DerivedCategory.Q.map (stageInclusion h F ((OrderDual.ofDual m : ℕ+) : ℕ)) ≫
        (positiveDerivedSystem I F).map f := sorry

/-- The natural transformation of derived ideal-power systems induced by `I' ≤ I`. -/
noncomputable def idealPowerSystemInclusion {I I' : X.IdealSheafData} (h : I' ≤ I)
    (F : CochainComplex X.Modules ℤ) :
    positiveDerivedSystem I' F ⟶ positiveDerivedSystem I F where
  app n := DerivedCategory.Q.map (stageInclusion h F ((OrderDual.ofDual n : ℕ+) : ℕ))
  naturality := fun {_ _} f ↦ systemInclusion_naturality h F f

/-- At every positive stage, `idealPowerSystemInclusion` is the localization of the canonical
inclusion `(I') ^ n F ⟶ I ^ n F`. -/
theorem idealPowerSystemInclusion_app {I I' : X.IdealSheafData} (h : I' ≤ I)
    (F : CochainComplex X.Modules ℤ) (n : OrderDual ℕ+) :
    (idealPowerSystemInclusion h F).app n =
      DerivedCategory.Q.map
        (stageInclusion h F ((OrderDual.ofDual n : ℕ+) : ℕ)) := sorry

end AlgebraicGeometry.Scheme.Modules.IdealPowerComplex

namespace AlgebraicGeometry.Scheme.ModuleDerived.DeligneSystem

open Scheme.Modules.IdealPowerComplex

variable {X U U' : Scheme.{v}}

/-- Forgetting boundedness and coherence identifies bounded restriction with ambient derived
pullback. -/
noncomputable def restrictionAmbientIso
    {Y Z : Scheme.{v}} (f : Y ⟶ Z)
    [IsNoetherian Y] [IsNoetherian Z] [IsOpenImmersion f] :
    restriction f ⋙ ambient (SheafOfModules.isCoherent Y.ringCatSheaf) ≅
      ambient (SheafOfModules.isCoherent Z.ringCatSheaf) ⋙
        RingedSpace.modulePullbackDerived f.toShHom :=
  (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight
      ((DerivedCategory.Bounded.cohomologyIn
        (SheafOfModules.isCoherent Y.ringCatSheaf) :
          ObjectProperty (DerivedCategory.Bounded Y.Modules)).liftCompιIso
        (restrictionInBounded f) (restrictionInBounded_obj_coherent f))
      DerivedCategory.Bounded.ι ≪≫
    (t.bounded : ObjectProperty (DerivedCategory Y.Modules)).liftCompιIso
      (ambient (SheafOfModules.isCoherent Z.ringCatSheaf) ⋙
        RingedSpace.modulePullbackDerived f.toShHom) (restriction_obj_bounded f)

/-- Bounded coherent restriction along two open immersions agrees with restriction along their
composite. -/
noncomputable def restrictionCompIso
    (i : U' ⟶ U) (j : U ⟶ X)
    [IsNoetherian X] [IsNoetherian U] [IsNoetherian U']
    [IsOpenImmersion i] [IsOpenImmersion j] :
    restriction j ⋙ restriction i ≅ restriction (i ≫ j) :=
  ((Functor.FullyFaithful.ofFullyFaithful
      (ambient (SheafOfModules.isCoherent U'.ringCatSheaf))).whiskeringRight
        Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf]).preimageIso <|
    Functor.isoWhiskerLeft (restriction j) (restrictionAmbientIso i) ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerRight (restrictionAmbientIso j)
        (RingedSpace.modulePullbackDerived i.toShHom) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerLeft (ambient (SheafOfModules.isCoherent X.ringCatSheaf))
        (RingedSpace.modulePullbackDerived.compIso i.toShHom j.toShHom
          (RingedSpace.modulePullbackDerived.compComparison_isIso i.toShHom j.toShHom)) ≪≫
      (restrictionAmbientIso (i ≫ j)).symm

/-- After forgetting boundedness and coherence, the bounded restriction-composition comparison
is the canonical derived-pullback comparison. -/
theorem restrictionCompIso_ambient
    (i : U' ⟶ U) (j : U ⟶ X)
    [IsNoetherian X] [IsNoetherian U] [IsNoetherian U']
    [IsOpenImmersion i] [IsOpenImmersion j]
    (L : Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf]) :
    (ambient (SheafOfModules.isCoherent U'.ringCatSheaf)).map
        ((restrictionCompIso i j).hom.app L) =
      (restrictionAmbientIso i).hom.app ((restriction j).obj L) ≫
        (RingedSpace.modulePullbackDerived i.toShHom).map
          ((restrictionAmbientIso j).hom.app L) ≫
        (RingedSpace.modulePullbackDerived.compComparison i.toShHom j.toShHom).app
          ((ambient (SheafOfModules.isCoherent X.ringCatSheaf)).obj L) ≫
        (restrictionAmbientIso (i ≫ j)).inv.app L := sorry

/-- A morphism between extension-by-zero objects realizes restriction from `U` to `U'` when
its action on maps to bounded coherent targets is the map induced by derived restriction. -/
def IsExtensionByZeroRestriction
    (i : U' ⟶ U) (j : U ⟶ X)
    [IsNoetherian X] [IsNoetherian U] [IsNoetherian U']
    [IsOpenImmersion i] [IsOpenImmersion j]
    (K : Dᵇ[SheafOfModules.isCoherent U.ringCatSheaf])
    (K' : Dᵇ[SheafOfModules.isCoherent U'.ringCatSheaf])
    (restrictionIso : K' ≅ (restriction i).obj K)
    (f : (extensionByZero (i ≫ j)).obj K' ⟶ (extensionByZero j).obj K) : Prop :=
  ∀ (L : Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf])
    (a : (extensionByZero j).obj K ⟶ Pro.yoneda.obj L),
    extensionByZeroHomMap (i ≫ j) K' L (f ≫ a) =
      restrictionIso.hom ≫
        (restriction i).map (extensionByZeroHomMap j K L a) ≫
        (restrictionCompIso i j).hom.app L

/-- The defining Hom-map equation for an extension-by-zero restriction morphism. -/
theorem isExtensionByZeroRestriction_iff
    (i : U' ⟶ U) (j : U ⟶ X)
    [IsNoetherian X] [IsNoetherian U] [IsNoetherian U']
    [IsOpenImmersion i] [IsOpenImmersion j]
    (K : Dᵇ[SheafOfModules.isCoherent U.ringCatSheaf])
    (K' : Dᵇ[SheafOfModules.isCoherent U'.ringCatSheaf])
    (restrictionIso : K' ≅ (restriction i).obj K)
    (f : (extensionByZero (i ≫ j)).obj K' ⟶ (extensionByZero j).obj K) :
    IsExtensionByZeroRestriction i j K K' restrictionIso f ↔
      ∀ (L : Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf])
        (a : (extensionByZero j).obj K ⟶ Pro.yoneda.obj L),
        extensionByZeroHomMap (i ≫ j) K' L (f ≫ a) =
          restrictionIso.hom ≫
            (restriction i).map (extensionByZeroHomMap j K L a) ≫
            (restrictionCompIso i j).hom.app L := Iff.rfl

/-- Restriction from `U` to `U'` induces a unique morphism between the corresponding
extension-by-zero objects. -/
theorem existsUnique_extensionByZeroRestriction
    (i : U' ⟶ U) (j : U ⟶ X)
    [IsNoetherian X] [IsNoetherian U] [IsNoetherian U']
    [IsOpenImmersion i] [IsOpenImmersion j]
    (K : Dᵇ[SheafOfModules.isCoherent U.ringCatSheaf])
    (K' : Dᵇ[SheafOfModules.isCoherent U'.ringCatSheaf])
    (restrictionIso : K' ≅ (restriction i).obj K) :
    ∃! f : (extensionByZero (i ≫ j)).obj K' ⟶ (extensionByZero j).obj K,
      IsExtensionByZeroRestriction i j K K' restrictionIso f := sorry

/-- The canonical restriction morphisms between extension-by-zero objects are natural in
restriction-compatible morphisms of bounded coherent derived objects. -/
theorem extensionByZeroRestriction_naturality
    (i : U' ⟶ U) (j : U ⟶ X)
    [IsNoetherian X] [IsNoetherian U] [IsNoetherian U']
    [IsOpenImmersion i] [IsOpenImmersion j]
    {K L : Dᵇ[SheafOfModules.isCoherent U.ringCatSheaf]}
    {K' L' : Dᵇ[SheafOfModules.isCoherent U'.ringCatSheaf]}
    (restrictionIsoK : K' ≅ (restriction i).obj K)
    (restrictionIsoL : L' ≅ (restriction i).obj L)
    (f : K ⟶ L) (f' : K' ⟶ L')
    (h_compatible : f' ≫ restrictionIsoL.hom =
      restrictionIsoK.hom ≫ (restriction i).map f)
    (rK : (extensionByZero (i ≫ j)).obj K' ⟶ (extensionByZero j).obj K)
    (rL : (extensionByZero (i ≫ j)).obj L' ⟶ (extensionByZero j).obj L)
    (hrK : IsExtensionByZeroRestriction i j K K' restrictionIsoK rK)
    (hrL : IsExtensionByZeroRestriction i j L L' restrictionIsoL rL) :
    (extensionByZero (i ≫ j)).map f' ≫ rL =
      rK ≫ (extensionByZero j).map f := sorry

/-- Naturality of the bounded lifts of the inclusions between two ideal-power systems. -/
theorem boundedIdealPowerSystemInclusion_naturality
    (i : U' ⟶ U) (j : U ⟶ X)
    [IsNoetherian X] [IsNoetherian U] [IsNoetherian U']
    [IsOpenImmersion i] [IsOpenImmersion j]
    (K : Dᵇ[SheafOfModules.isCoherent U.ringCatSheaf])
    (K' : Dᵇ[SheafOfModules.isCoherent U'.ringCatSheaf])
    (I I' : X.IdealSheafData)
    (F : CochainComplex.BoundedTermsIn (SheafOfModules.isCoherent X.ringCatSheaf))
    (hU : I.openComplement = j.opensRange)
    (hU' : I'.openComplement = (i ≫ j).opensRange)
    (h : I' ≤ I)
    (systemIso :
      positiveDerivedSystem I F.obj ⋙ RingedSpace.modulePullbackDerived j.toShHom ≅
        (Functor.const (OrderDual ℕ+)).obj
          ((ambient (SheafOfModules.isCoherent U.ringCatSheaf)).obj K))
    (systemIso' :
      positiveDerivedSystem I' F.obj ⋙
          RingedSpace.modulePullbackDerived (i ≫ j).toShHom ≅
        (Functor.const (OrderDual ℕ+)).obj
          ((ambient (SheafOfModules.isCoherent U'.ringCatSheaf)).obj K'))
    {m n : OrderDual ℕ+} (f : m ⟶ n) :
    (boundedTower (i ≫ j) (ofIdealPower (i ≫ j) I' F hU' K' systemIso')).map f ≫
        (ambient (SheafOfModules.isCoherent X.ringCatSheaf)).preimage
          ((boundedTowerAmbientIso (i ≫ j)
              (ofIdealPower (i ≫ j) I' F hU' K' systemIso')).hom.app n ≫
            (idealPowerSystemInclusion h F.obj).app n ≫
            (boundedTowerAmbientIso j
              (ofIdealPower j I F hU K systemIso)).inv.app n) =
      (ambient (SheafOfModules.isCoherent X.ringCatSheaf)).preimage
          ((boundedTowerAmbientIso (i ≫ j)
              (ofIdealPower (i ≫ j) I' F hU' K' systemIso')).hom.app m ≫
            (idealPowerSystemInclusion h F.obj).app m ≫
            (boundedTowerAmbientIso j
              (ofIdealPower j I F hU K systemIso)).inv.app m) ≫
        (boundedTower j (ofIdealPower j I F hU K systemIso)).map f := sorry

/-- The natural transformation between bounded coherent ideal-power towers induced by
`I' ≤ I`. -/
noncomputable def boundedIdealPowerSystemInclusion
    (i : U' ⟶ U) (j : U ⟶ X)
    [IsNoetherian X] [IsNoetherian U] [IsNoetherian U']
    [IsOpenImmersion i] [IsOpenImmersion j]
    (K : Dᵇ[SheafOfModules.isCoherent U.ringCatSheaf])
    (K' : Dᵇ[SheafOfModules.isCoherent U'.ringCatSheaf])
    (I I' : X.IdealSheafData)
    (F : CochainComplex.BoundedTermsIn (SheafOfModules.isCoherent X.ringCatSheaf))
    (hU : I.openComplement = j.opensRange)
    (hU' : I'.openComplement = (i ≫ j).opensRange)
    (h : I' ≤ I)
    (systemIso :
      positiveDerivedSystem I F.obj ⋙ RingedSpace.modulePullbackDerived j.toShHom ≅
        (Functor.const (OrderDual ℕ+)).obj
          ((ambient (SheafOfModules.isCoherent U.ringCatSheaf)).obj K))
    (systemIso' :
      positiveDerivedSystem I' F.obj ⋙
          RingedSpace.modulePullbackDerived (i ≫ j).toShHom ≅
        (Functor.const (OrderDual ℕ+)).obj
          ((ambient (SheafOfModules.isCoherent U'.ringCatSheaf)).obj K')) :
    boundedTower (i ≫ j) (ofIdealPower (i ≫ j) I' F hU' K' systemIso') ⟶
      boundedTower j (ofIdealPower j I F hU K systemIso) where
  app n := (ambient (SheafOfModules.isCoherent X.ringCatSheaf)).preimage
    ((boundedTowerAmbientIso (i ≫ j)
        (ofIdealPower (i ≫ j) I' F hU' K' systemIso')).hom.app n ≫
      (idealPowerSystemInclusion h F.obj).app n ≫
      (boundedTowerAmbientIso j (ofIdealPower j I F hU K systemIso)).inv.app n)
  naturality := fun {_ _} f ↦ boundedIdealPowerSystemInclusion_naturality
    i j K K' I I' F hU hU' h systemIso systemIso' f

/-- Each component of the bounded ideal-power inclusion becomes the canonical ambient stage
inclusion after forgetting boundedness and coherence. -/
theorem boundedIdealPowerSystemInclusion_ambient_app
    (i : U' ⟶ U) (j : U ⟶ X)
    [IsNoetherian X] [IsNoetherian U] [IsNoetherian U']
    [IsOpenImmersion i] [IsOpenImmersion j]
    (K : Dᵇ[SheafOfModules.isCoherent U.ringCatSheaf])
    (K' : Dᵇ[SheafOfModules.isCoherent U'.ringCatSheaf])
    (I I' : X.IdealSheafData)
    (F : CochainComplex.BoundedTermsIn (SheafOfModules.isCoherent X.ringCatSheaf))
    (hU : I.openComplement = j.opensRange)
    (hU' : I'.openComplement = (i ≫ j).opensRange)
    (h : I' ≤ I)
    (systemIso :
      positiveDerivedSystem I F.obj ⋙ RingedSpace.modulePullbackDerived j.toShHom ≅
        (Functor.const (OrderDual ℕ+)).obj
          ((ambient (SheafOfModules.isCoherent U.ringCatSheaf)).obj K))
    (systemIso' :
      positiveDerivedSystem I' F.obj ⋙
          RingedSpace.modulePullbackDerived (i ≫ j).toShHom ≅
        (Functor.const (OrderDual ℕ+)).obj
          ((ambient (SheafOfModules.isCoherent U'.ringCatSheaf)).obj K'))
    (n : OrderDual ℕ+) :
    (ambient (SheafOfModules.isCoherent X.ringCatSheaf)).map
        ((boundedIdealPowerSystemInclusion i j K K' I I' F hU hU' h
          systemIso systemIso').app n) =
      (boundedTowerAmbientIso (i ≫ j)
          (ofIdealPower (i ≫ j) I' F hU' K' systemIso')).hom.app n ≫
        (idealPowerSystemInclusion h F.obj).app n ≫
        (boundedTowerAmbientIso j
          (ofIdealPower j I F hU K systemIso)).inv.app n := sorry

/-- The bounded coherent Pro morphism represented by the inclusions
`(I') ^ n F ⟶ I ^ n F`, transported through explicit presentation isomorphisms. -/
noncomputable def idealPowerCompactSupportMap
    (i : U' ⟶ U) (j : U ⟶ X)
    [IsNoetherian X] [IsNoetherian U] [IsNoetherian U']
    [IsOpenImmersion i] [IsOpenImmersion j]
    (K : Dᵇ[SheafOfModules.isCoherent U.ringCatSheaf])
    (K' : Dᵇ[SheafOfModules.isCoherent U'.ringCatSheaf])
    (I I' : X.IdealSheafData)
    (F : CochainComplex.BoundedTermsIn (SheafOfModules.isCoherent X.ringCatSheaf))
    (hU : I.openComplement = j.opensRange)
    (hU' : I'.openComplement = (i ≫ j).opensRange)
    (h : I' ≤ I)
    (systemIso :
      positiveDerivedSystem I F.obj ⋙ RingedSpace.modulePullbackDerived j.toShHom ≅
        (Functor.const (OrderDual ℕ+)).obj
          ((ambient (SheafOfModules.isCoherent U.ringCatSheaf)).obj K))
    (systemIso' :
      positiveDerivedSystem I' F.obj ⋙
          RingedSpace.modulePullbackDerived (i ≫ j).toShHom ≅
        (Functor.const (OrderDual ℕ+)).obj
          ((ambient (SheafOfModules.isCoherent U'.ringCatSheaf)).obj K'))
    (sourceIso : boundedProObject (i ≫ j)
        (ofIdealPower (i ≫ j) I' F hU' K' systemIso') ≅
      (extensionByZero (i ≫ j)).obj K')
    (targetIso : boundedProObject j (ofIdealPower j I F hU K systemIso) ≅
      (extensionByZero j).obj K) :
    (extensionByZero (i ≫ j)).obj K' ⟶ (extensionByZero j).obj K :=
  sourceIso.inv ≫
    (@Pro.lim Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf] _
      (OrderDual ℕ+) _ _ _ _).map
      (boundedIdealPowerSystemInclusion i j K K' I I' F hU hU' h
        systemIso systemIso') ≫
    targetIso.hom

/-- Two ideal-power presentations are compatible when their stagewise inclusions and bounded
presentation comparisons induce the canonical restriction map. -/
def CompatibleIdealPowerPresentations
    (i : U' ⟶ U) (j : U ⟶ X)
    [IsNoetherian X] [IsNoetherian U] [IsNoetherian U']
    [IsOpenImmersion i] [IsOpenImmersion j]
    (K : Dᵇ[SheafOfModules.isCoherent U.ringCatSheaf])
    (K' : Dᵇ[SheafOfModules.isCoherent U'.ringCatSheaf])
    (restrictionIso : K' ≅ (restriction i).obj K)
    (I I' : X.IdealSheafData)
    (F : CochainComplex.BoundedTermsIn (SheafOfModules.isCoherent X.ringCatSheaf))
    (hU : I.openComplement = j.opensRange)
    (hU' : I'.openComplement = (i ≫ j).opensRange)
    (h : I' ≤ I)
    (systemIso :
      positiveDerivedSystem I F.obj ⋙ RingedSpace.modulePullbackDerived j.toShHom ≅
        (Functor.const (OrderDual ℕ+)).obj
          ((ambient (SheafOfModules.isCoherent U.ringCatSheaf)).obj K))
    (systemIso' :
      positiveDerivedSystem I' F.obj ⋙
          RingedSpace.modulePullbackDerived (i ≫ j).toShHom ≅
        (Functor.const (OrderDual ℕ+)).obj
          ((ambient (SheafOfModules.isCoherent U'.ringCatSheaf)).obj K'))
    (sourceIso : boundedProObject (i ≫ j)
        (ofIdealPower (i ≫ j) I' F hU' K' systemIso') ≅
      (extensionByZero (i ≫ j)).obj K')
    (targetIso : boundedProObject j (ofIdealPower j I F hU K systemIso) ≅
      (extensionByZero j).obj K) : Prop :=
  (∀ n : OrderDual ℕ+,
    (RingedSpace.modulePullbackDerived.compComparison i.toShHom j.toShHom).app
        ((positiveDerivedSystem I' F.obj).obj n) ≫
      systemIso'.hom.app n ≫
        (ambient (SheafOfModules.isCoherent U'.ringCatSheaf)).map restrictionIso.hom =
    (RingedSpace.modulePullbackDerived i.toShHom).map
        ((RingedSpace.modulePullbackDerived j.toShHom).map
          ((idealPowerSystemInclusion h F.obj).app n)) ≫
      (RingedSpace.modulePullbackDerived i.toShHom).map (systemIso.hom.app n)) ∧
  (∀ (L : Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf])
    (a : (extensionByZero j).obj K ⟶ Pro.yoneda.obj L),
    extensionByZeroHomMap (i ≫ j) K' L
        (idealPowerCompactSupportMap i j K K' I I' F hU hU' h systemIso systemIso'
          sourceIso targetIso ≫ a) =
      restrictionIso.hom ≫
        (restriction i).map (extensionByZeroHomMap j K L a) ≫
        (restrictionCompIso i j).hom.app L)

/-- The stagewise and presentation-comparison equations characterizing compatible ideal-power
presentations. -/
theorem compatibleIdealPowerPresentations_iff
    (i : U' ⟶ U) (j : U ⟶ X)
    [IsNoetherian X] [IsNoetherian U] [IsNoetherian U']
    [IsOpenImmersion i] [IsOpenImmersion j]
    (K : Dᵇ[SheafOfModules.isCoherent U.ringCatSheaf])
    (K' : Dᵇ[SheafOfModules.isCoherent U'.ringCatSheaf])
    (restrictionIso : K' ≅ (restriction i).obj K)
    (I I' : X.IdealSheafData)
    (F : CochainComplex.BoundedTermsIn (SheafOfModules.isCoherent X.ringCatSheaf))
    (hU : I.openComplement = j.opensRange)
    (hU' : I'.openComplement = (i ≫ j).opensRange)
    (h : I' ≤ I)
    (systemIso :
      positiveDerivedSystem I F.obj ⋙ RingedSpace.modulePullbackDerived j.toShHom ≅
        (Functor.const (OrderDual ℕ+)).obj
          ((ambient (SheafOfModules.isCoherent U.ringCatSheaf)).obj K))
    (systemIso' :
      positiveDerivedSystem I' F.obj ⋙
          RingedSpace.modulePullbackDerived (i ≫ j).toShHom ≅
        (Functor.const (OrderDual ℕ+)).obj
          ((ambient (SheafOfModules.isCoherent U'.ringCatSheaf)).obj K'))
    (sourceIso : boundedProObject (i ≫ j)
        (ofIdealPower (i ≫ j) I' F hU' K' systemIso') ≅
      (extensionByZero (i ≫ j)).obj K')
    (targetIso : boundedProObject j (ofIdealPower j I F hU K systemIso) ≅
      (extensionByZero j).obj K) :
    CompatibleIdealPowerPresentations i j K K' restrictionIso I I' F hU hU' h
        systemIso systemIso' sourceIso targetIso ↔
      ((∀ n : OrderDual ℕ+,
        (RingedSpace.modulePullbackDerived.compComparison i.toShHom j.toShHom).app
            ((positiveDerivedSystem I' F.obj).obj n) ≫
          systemIso'.hom.app n ≫
            (ambient (SheafOfModules.isCoherent U'.ringCatSheaf)).map restrictionIso.hom =
        (RingedSpace.modulePullbackDerived i.toShHom).map
            ((RingedSpace.modulePullbackDerived j.toShHom).map
              ((idealPowerSystemInclusion h F.obj).app n)) ≫
          (RingedSpace.modulePullbackDerived i.toShHom).map (systemIso.hom.app n)) ∧
      (∀ (L : Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf])
        (a : (extensionByZero j).obj K ⟶ Pro.yoneda.obj L),
        extensionByZeroHomMap (i ≫ j) K' L
            (idealPowerCompactSupportMap i j K K' I I' F hU hU' h systemIso systemIso'
              sourceIso targetIso ≫ a) =
          restrictionIso.hom ≫
            (restriction i).map (extensionByZeroHomMap j K L a) ≫
            (restrictionCompIso i j).hom.app L)) := Iff.rfl

/-- Compatible ideal-power presentations realize the canonical compact-support restriction
morphism through the localized stage inclusions. -/
theorem idealPowerCompactSupportMap_isRestriction
    (i : U' ⟶ U) (j : U ⟶ X)
    [IsNoetherian X] [IsNoetherian U] [IsNoetherian U']
    [IsOpenImmersion i] [IsOpenImmersion j]
    (K : Dᵇ[SheafOfModules.isCoherent U.ringCatSheaf])
    (K' : Dᵇ[SheafOfModules.isCoherent U'.ringCatSheaf])
    (restrictionIso : K' ≅ (restriction i).obj K)
    (I I' : X.IdealSheafData)
    (F : CochainComplex.BoundedTermsIn (SheafOfModules.isCoherent X.ringCatSheaf))
    (hU : I.openComplement = j.opensRange)
    (hU' : I'.openComplement = (i ≫ j).opensRange)
    (h : I' ≤ I)
    (systemIso :
      positiveDerivedSystem I F.obj ⋙ RingedSpace.modulePullbackDerived j.toShHom ≅
        (Functor.const (OrderDual ℕ+)).obj
          ((ambient (SheafOfModules.isCoherent U.ringCatSheaf)).obj K))
    (systemIso' :
      positiveDerivedSystem I' F.obj ⋙
          RingedSpace.modulePullbackDerived (i ≫ j).toShHom ≅
        (Functor.const (OrderDual ℕ+)).obj
          ((ambient (SheafOfModules.isCoherent U'.ringCatSheaf)).obj K'))
    (sourceIso : boundedProObject (i ≫ j)
        (ofIdealPower (i ≫ j) I' F hU' K' systemIso') ≅
      (extensionByZero (i ≫ j)).obj K')
    (targetIso : boundedProObject j (ofIdealPower j I F hU K systemIso) ≅
      (extensionByZero j).obj K)
    (h_presentations : CompatibleIdealPowerPresentations i j K K' restrictionIso
      I I' F hU hU' h systemIso systemIso' sourceIso targetIso) :
    IsExtensionByZeroRestriction i j K K' restrictionIso
      (idealPowerCompactSupportMap i j K K' I I' F hU hU' h systemIso systemIso'
        sourceIso targetIso) := sorry

end AlgebraicGeometry.Scheme.ModuleDerived.DeligneSystem
