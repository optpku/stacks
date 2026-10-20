module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Completion.FormalFunctions
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.IdealPower.Quotient
public import ReasLib.Topology.Sheaf.Cohomology.SupportedRestriction
public import ReasLib.AlgebraicGeometry.PuncturedSpectrum

/-!
# Cohomology comparisons on punctured spectra

Cohomology on an open containing the ideal support maps to the inverse limit of
ideal-power quotient cohomology. A separate construction retains cohomology of
ordinary direct images of restrictions, with the positive quotient tower.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open SheafOfModules.RingedSite.IdealSheaf
open SheafOfModules.RingedSite.IdealSheaf.PowerQuotientModule

noncomputable section

universe u

namespace AlgebraicGeometry.PuncturedSpectrum

open Scheme Scheme.ModuleDerived.DerivedCompletion

variable {A : Type u} [CommRing A] [IsLocalRing A]

/-- Degree-`i` cohomology on the punctured spectrum of the ordinary direct image
of the restriction of `M` to `V`. -/
noncomputable abbrev directImageCohomology
    (M : (scheme A).Modules) (V : (scheme A).Opens) (i : ℕ) :
    ModuleCat.{u} A :=
  ((ModuleCech.moduleToDerived (scheme A) ⋙
      Scheme.FlatPullbackSections.baseSections (puncturedOpen A).ι ⋙
      DerivedCategory.homologyFunctor (ModuleCat.{u} A) (i : ℤ)).obj
    ((Scheme.Modules.pushforward V.ι).obj
      ((Scheme.Modules.pullback V.ι).obj M)))

/-- Restriction of a positive quotient to a neighborhood containing its support is bijective on
sections over every open. -/
theorem positiveQuotientUnitApp_bijective
    (I : Ideal A) (M : (scheme A).Modules) (V : (scheme A).Opens)
    (hV : (((idealSheafDataOfIdealOnSpec I).comap
      (puncturedOpen A).ι).support : Set (scheme A)) ⊆ (V : Set (scheme A)))
    (n : ℕ) (W : ((scheme A).Opens)ᵒᵖ) :
    Function.Bijective
      (((Scheme.Modules.pullbackPushforwardAdjunction V.ι).unit.app
        (Scheme.Hom.IdealPowerCohomology.Quotient.stage I (puncturedOpen A).ι M (n + 1))).val.app W).hom := sorry

/-- The objectwise extension of sections of a positive quotient from a neighborhood containing
its support. Its underlying function is the canonical inverse function of restriction. -/
noncomputable def positiveQuotientUnitInverseApp
    (I : Ideal A) (M : (scheme A).Modules) (V : (scheme A).Opens)
    (hV : (((idealSheafDataOfIdealOnSpec I).comap
      (puncturedOpen A).ι).support : Set (scheme A)) ⊆ (V : Set (scheme A)))
    (n : ℕ) (W : ((scheme A).Opens)ᵒᵖ) :
    ((Scheme.Modules.pushforward V.ι).obj
        ((Scheme.Modules.pullback V.ι).obj (Scheme.Hom.IdealPowerCohomology.Quotient.stage I (puncturedOpen A).ι M (n + 1)))).val.obj W ⟶
      (Scheme.Hom.IdealPowerCohomology.Quotient.stage I (puncturedOpen A).ι M (n + 1)).val.obj W :=
  let f := (((Scheme.Modules.pullbackPushforwardAdjunction V.ι).unit.app
    (Scheme.Hom.IdealPowerCohomology.Quotient.stage I (puncturedOpen A).ι M (n + 1))).val.app W)
  let linearEquiv := LinearEquiv.ofBijective f.hom
    (positiveQuotientUnitApp_bijective I M V hV n W)
  ConcreteCategory.ofHom linearEquiv.symm.toLinearMap

/-- Objectwise supported-section extension is the inverse-function construction applied to the
restriction map. -/
theorem positiveQuotientUnitInverseApp_apply
    (I : Ideal A) (M : (scheme A).Modules) (V : (scheme A).Opens)
    (hV : (((idealSheafDataOfIdealOnSpec I).comap
      (puncturedOpen A).ι).support : Set (scheme A)) ⊆ (V : Set (scheme A)))
    (n : ℕ) (W : ((scheme A).Opens)ᵒᵖ)
    (x : ((Scheme.Modules.pushforward V.ι).obj
      ((Scheme.Modules.pullback V.ι).obj (Scheme.Hom.IdealPowerCohomology.Quotient.stage I (puncturedOpen A).ι M (n + 1)))).val.obj W) :
    positiveQuotientUnitInverseApp I M V hV n W x =
      Function.invFun
        (((Scheme.Modules.pullbackPushforwardAdjunction V.ι).unit.app
          (Scheme.Hom.IdealPowerCohomology.Quotient.stage I (puncturedOpen A).ι M (n + 1))).val.app W).hom x := sorry

/-- The objectwise supported-section extensions commute with restriction maps. -/
theorem positiveQuotientUnitInverseApp_naturality
    (I : Ideal A) (M : (scheme A).Modules) (V : (scheme A).Opens)
    (hV : (((idealSheafDataOfIdealOnSpec I).comap
      (puncturedOpen A).ι).support : Set (scheme A)) ⊆ (V : Set (scheme A)))
    (n : ℕ) {W W' : ((scheme A).Opens)ᵒᵖ} (f : W ⟶ W') :
    ((Scheme.Modules.pushforward V.ι).obj
        ((Scheme.Modules.pullback V.ι).obj (Scheme.Hom.IdealPowerCohomology.Quotient.stage I (puncturedOpen A).ι M (n + 1)))).val.map f ≫
        (ModuleCat.restrictScalars ((scheme A).ringCatSheaf.obj.map f).hom).map
          (positiveQuotientUnitInverseApp I M V hV n W') =
      positiveQuotientUnitInverseApp I M V hV n W ≫
        (Scheme.Hom.IdealPowerCohomology.Quotient.stage I (puncturedOpen A).ι M (n + 1)).val.map f := sorry

/-- The explicit extension-by-support morphism from the direct image of the restricted positive
quotient back to the positive quotient on the punctured spectrum. -/
noncomputable def positiveQuotientUnitInverse
    (I : Ideal A) (M : (scheme A).Modules) (V : (scheme A).Opens)
    (hV : (((idealSheafDataOfIdealOnSpec I).comap
      (puncturedOpen A).ι).support : Set (scheme A)) ⊆ (V : Set (scheme A)))
    (n : ℕ) :
    (Scheme.Modules.pushforward V.ι).obj
        ((Scheme.Modules.pullback V.ι).obj (Scheme.Hom.IdealPowerCohomology.Quotient.stage I (puncturedOpen A).ι M (n + 1))) ⟶
      Scheme.Hom.IdealPowerCohomology.Quotient.stage I (puncturedOpen A).ι M (n + 1) :=
  { val :=
      { app := positiveQuotientUnitInverseApp I M V hV n
        naturality := positiveQuotientUnitInverseApp_naturality I M V hV n } }

/-- Restriction followed by explicit supported-section extension is the identity on a positive
quotient. -/
theorem positiveQuotientUnit_comp_inverse
    (I : Ideal A) (M : (scheme A).Modules) (V : (scheme A).Opens)
    (hV : (((idealSheafDataOfIdealOnSpec I).comap
      (puncturedOpen A).ι).support : Set (scheme A)) ⊆ (V : Set (scheme A)))
    (n : ℕ) :
    (Scheme.Modules.pullbackPushforwardAdjunction V.ι).unit.app
        (Scheme.Hom.IdealPowerCohomology.Quotient.stage I (puncturedOpen A).ι M (n + 1)) ≫ positiveQuotientUnitInverse I M V hV n =
      𝟙 (Scheme.Hom.IdealPowerCohomology.Quotient.stage I (puncturedOpen A).ι M (n + 1)) := sorry

/-- Explicit supported-section extension followed by restriction is the identity on the direct
image of the restricted positive quotient. -/
theorem positiveQuotientInverse_comp_unit
    (I : Ideal A) (M : (scheme A).Modules) (V : (scheme A).Opens)
    (hV : (((idealSheafDataOfIdealOnSpec I).comap
      (puncturedOpen A).ι).support : Set (scheme A)) ⊆ (V : Set (scheme A)))
    (n : ℕ) :
    positiveQuotientUnitInverse I M V hV n ≫
        (Scheme.Modules.pullbackPushforwardAdjunction V.ι).unit.app
          (Scheme.Hom.IdealPowerCohomology.Quotient.stage I (puncturedOpen A).ι M (n + 1)) =
      𝟙 ((Scheme.Modules.pushforward V.ι).obj
        ((Scheme.Modules.pullback V.ι).obj (Scheme.Hom.IdealPowerCohomology.Quotient.stage I (puncturedOpen A).ι M (n + 1)))) := sorry

/-- The restriction unit for a positive quotient, with its inverse given by explicit
supported-section extension. -/
noncomputable def positiveQuotientUnitIso
    (I : Ideal A) (M : (scheme A).Modules) (V : (scheme A).Opens)
    (hV : (((idealSheafDataOfIdealOnSpec I).comap
      (puncturedOpen A).ι).support : Set (scheme A)) ⊆ (V : Set (scheme A)))
    (n : ℕ) :
    Scheme.Hom.IdealPowerCohomology.Quotient.stage I (puncturedOpen A).ι M (n + 1) ≅
      (Scheme.Modules.pushforward V.ι).obj
        ((Scheme.Modules.pullback V.ι).obj (Scheme.Hom.IdealPowerCohomology.Quotient.stage I (puncturedOpen A).ι M (n + 1))) where
  hom := (Scheme.Modules.pullbackPushforwardAdjunction V.ι).unit.app
    (Scheme.Hom.IdealPowerCohomology.Quotient.stage I (puncturedOpen A).ι M (n + 1))
  inv := positiveQuotientUnitInverse I M V hV n
  hom_inv_id := positiveQuotientUnit_comp_inverse I M V hV n
  inv_hom_id := positiveQuotientInverse_comp_unit I M V hV n

/-- The map from cohomology of the ordinary direct image of a restricted positive
quotient to the positive quotient-cohomology stage on the punctured spectrum. -/
noncomputable def quotientCohomologyExtension
    (I : Ideal A) (M : (scheme A).Modules) (V : (scheme A).Opens)
    (hV : (((idealSheafDataOfIdealOnSpec I).comap
      (puncturedOpen A).ι).support : Set (scheme A)) ⊆ (V : Set (scheme A)))
    (i n : ℕ) :
    directImageCohomology (Scheme.Hom.IdealPowerCohomology.Quotient.stage I (puncturedOpen A).ι M (n + 1)) V i ⟶
      (quotientCohomologySystem (puncturedOpen A).ι I M (i : ℤ)).obj (op n) :=
  (ModuleCech.moduleToDerived (scheme A) ⋙
      Scheme.FlatPullbackSections.baseSections (puncturedOpen A).ι ⋙
      DerivedCategory.homologyFunctor (ModuleCat.{u} A) (i : ℤ)).map
    (positiveQuotientUnitInverse I M V hV n) ≫
    eqToHom (quotientCohomologySystem_obj
      (puncturedOpen A).ι I M (i : ℤ) n).symm

/-- Extending quotient cohomology from `V` and then restricting it back along the
pullback-pushforward unit is the identity. -/
theorem quotientCohomologyExtension_spec
    (I : Ideal A) (M : (scheme A).Modules) (V : (scheme A).Opens)
    (hV : (((idealSheafDataOfIdealOnSpec I).comap
      (puncturedOpen A).ι).support : Set (scheme A)) ⊆ (V : Set (scheme A)))
    (i n : ℕ) :
    quotientCohomologyExtension I M V hV i n ≫
        eqToHom (quotientCohomologySystem_obj
          (puncturedOpen A).ι I M (i : ℤ) n) ≫
        (ModuleCech.moduleToDerived (scheme A) ⋙
          Scheme.FlatPullbackSections.baseSections (puncturedOpen A).ι ⋙
          DerivedCategory.homologyFunctor (ModuleCat.{u} A) (i : ℤ)).map
            ((Scheme.Modules.pullbackPushforwardAdjunction V.ι).unit.app
              (Scheme.Hom.IdealPowerCohomology.Quotient.stage I (puncturedOpen A).ι M (n + 1))) =
      𝟙 (directImageCohomology (Scheme.Hom.IdealPowerCohomology.Quotient.stage I (puncturedOpen A).ι M (n + 1)) V i) := sorry

/-- The map from direct-image cohomology to the `n`th positive quotient-cohomology
stage: first take the quotient on `V`, then extend from its support. -/
noncomputable def cohomologyProjection
    (I : Ideal A) (M : (scheme A).Modules) (V : (scheme A).Opens)
    (hV : (((idealSheafDataOfIdealOnSpec I).comap
      (puncturedOpen A).ι).support : Set (scheme A)) ⊆ (V : Set (scheme A)))
    (i n : ℕ) :
    directImageCohomology M V i ⟶
      (quotientCohomologySystem (puncturedOpen A).ι I M (i : ℤ)).obj (op n) :=
  (ModuleCech.moduleToDerived (scheme A) ⋙
      Scheme.FlatPullbackSections.baseSections (puncturedOpen A).ι ⋙
      DerivedCategory.homologyFunctor (ModuleCat.{u} A) (i : ℤ)).map
        ((Scheme.Modules.pushforward V.ι).map
          ((Scheme.Modules.pullback V.ι).map (Scheme.Hom.IdealPowerCohomology.Quotient.projection I (puncturedOpen A).ι M (n + 1)))) ≫
    quotientCohomologyExtension I M V hV i n

/-- The direct-image cohomology projections commute with the transitions of the positive
quotient-cohomology system. -/
theorem cohomologyProjection_naturality
    (I : Ideal A) (M : (scheme A).Modules) (V : (scheme A).Opens)
    (hV : (((idealSheafDataOfIdealOnSpec I).comap
      (puncturedOpen A).ι).support : Set (scheme A)) ⊆ (V : Set (scheme A)))
    (i n : ℕ) :
    ((Functor.const ℕᵒᵖ).obj (directImageCohomology M V i)).map
          (homOfLE (Nat.le_add_right n 1)).op ≫
        cohomologyProjection I M V hV i n =
      cohomologyProjection I M V hV i (n + 1) ≫
        (quotientCohomologySystem (puncturedOpen A).ι I M (i : ℤ)).map
          (homOfLE (Nat.le_add_right n 1)).op := sorry

/-- The explicit cone from direct-image cohomology to the positive quotient-cohomology
system. -/
noncomputable def cohomologyCone
    (I : Ideal A) (M : (scheme A).Modules) (V : (scheme A).Opens)
    (hV : (((idealSheafDataOfIdealOnSpec I).comap
      (puncturedOpen A).ι).support : Set (scheme A)) ⊆ (V : Set (scheme A)))
    (i : ℕ) :
    Cone (quotientCohomologySystem (puncturedOpen A).ι I M (i : ℤ)) where
  pt := directImageCohomology M V i
  π := NatTrans.ofOpSequence (cohomologyProjection I M V hV i)
    (cohomologyProjection_naturality I M V hV i)

/-- The canonical morphism from degree-`i` cohomology of the ordinary direct image
of the restriction to `V` to the inverse limit of
cohomology of the positive `I`-power quotients on the punctured spectrum. -/
noncomputable def cohomologyComparison
    (I : Ideal A) (M : (scheme A).Modules) (V : (scheme A).Opens)
    (hV : (((idealSheafDataOfIdealOnSpec I).comap
      (puncturedOpen A).ι).support : Set (scheme A)) ⊆ (V : Set (scheme A)))
    (i : ℕ) :
    directImageCohomology M V i ⟶
      limit (quotientCohomologySystem (puncturedOpen A).ι I M (i : ℤ)) :=
  limit.lift _ (cohomologyCone I M V hV i)

/-- The `n`th limit projection of `cohomologyComparison` is the corresponding
quotient-cohomology projection. -/
theorem cohomologyComparison_π
    (I : Ideal A) (M : (scheme A).Modules) (V : (scheme A).Opens)
    (hV : (((idealSheafDataOfIdealOnSpec I).comap
      (puncturedOpen A).ι).support : Set (scheme A)) ⊆ (V : Set (scheme A)))
    (i n : ℕ) :
    cohomologyComparison I M V hV i ≫
        limit.π (quotientCohomologySystem (puncturedOpen A).ι I M (i : ℤ)) (op n) =
      cohomologyProjection I M V hV i n := sorry

/-- The canonical comparison is independent of the proof that the ideal support lies in
the chosen neighborhood. -/
theorem cohomologyComparison_proof_irrel
    (I : Ideal A) (M : (scheme A).Modules) (V : (scheme A).Opens)
    (hV hV' : (((idealSheafDataOfIdealOnSpec I).comap
      (puncturedOpen A).ι).support : Set (scheme A)) ⊆ (V : Set (scheme A)))
    (i : ℕ) :
    cohomologyComparison I M V hV i = cohomologyComparison I M V hV' i := sorry

/-- Degree-`i` cohomology of `M` on `V`, with scalars restricted from its section
ring along the punctured-spectrum morphism to `Spec A`. -/
noncomputable abbrev cohomologyOnOpen
    (M : (scheme A).Modules) (V : (scheme A).Opens) (i : ℕ) : ModuleCat.{u} A :=
  (ModuleCat.restrictScalars (Scheme.Hom.sectionsMap (puncturedOpen A).ι V)).obj
    (Scheme.Modules.moduleCohomologyAtOpen V M i)

/-- An ideal-power quotient has zero restriction to the complement of the pulled-back
ideal support. -/
theorem quotientRestrictionToComplement_eq_zero
    (I : Ideal A) (M : (scheme A).Modules) (n : ℕ) :
    TopCat.Sheaf.ClosedSubset.SectionsWithSupport.restrictionToComplement
      (((idealSheafDataOfIdealOnSpec I).comap (puncturedOpen A).ι).support.isClosed)
      ((SheafOfModules.toSheaf (scheme A).ringCatSheaf).obj
        (Scheme.Hom.IdealPowerCohomology.Quotient.stage I (puncturedOpen A).ι M n)) = 0 := sorry

/-- The quotient-and-supported-extension map on open cohomology commutes with
multiplication by every scalar from the base ring. -/
theorem openCohomologyStageMap_smul
    (I : Ideal A) (M : (scheme A).Modules) (V : (scheme A).Opens)
    (hV : (((idealSheafDataOfIdealOnSpec I).comap
      (puncturedOpen A).ι).support : Set (scheme A)) ⊆ (V : Set (scheme A)))
    (i n : ℕ) (a : A) :
    let additiveMap :=
      let Q := Scheme.Hom.IdealPowerCohomology.Quotient.stage I (puncturedOpen A).ι M n
      let toQuotient :=
        ((RingedSpace.moduleCohomologyAtOpenFunctor (scheme A).toRingedSpace V i) ⋙
          ModuleCat.restrictScalars (Scheme.Hom.sectionsMap (puncturedOpen A).ι V)).map
            (Scheme.Hom.IdealPowerCohomology.Quotient.projection I (puncturedOpen A).ι M n)
      (forget₂ (ModuleCat A) AddCommGrpCat).map toQuotient ≫
        eqToHom
          (Scheme.Modules.moduleCohomologyAtOpenForget_obj_eq_underlyingSheafCohomology V Q i) ≫
        TopCat.Sheaf.Cohomology.restrictionInverseOfSupport
          (((idealSheafDataOfIdealOnSpec I).comap (puncturedOpen A).ι).support.isClosed)
          ((SheafOfModules.toSheaf (scheme A).ringCatSheaf).obj Q)
          (quotientRestrictionToComplement_eq_zero I M n) i V hV ≫
        eqToHom (Scheme.Hom.cohomologyForget_obj_eq (puncturedOpen A).ι Q i).symm ≫
        (forget₂ (ModuleCat A) AddCommGrpCat).map
          (eqToHom (Scheme.Hom.IdealPowerCohomology.Quotient.tower_obj
            I (puncturedOpen A).ι M i n).symm)
    additiveMap ≫
        ((Scheme.Hom.IdealPowerCohomology.Quotient.tower I (puncturedOpen A).ι M i).obj
          (op n)).smul a =
      (cohomologyOnOpen M V i).smul a ≫
        additiveMap := sorry

/-- Cohomology on an open containing the ideal support maps to each quotient stage
by projection of coefficients followed by supported extension. -/
noncomputable def openCohomologyStageMap
    (I : Ideal A) (M : (scheme A).Modules) (V : (scheme A).Opens)
    (hV : (((idealSheafDataOfIdealOnSpec I).comap
      (puncturedOpen A).ι).support : Set (scheme A)) ⊆ (V : Set (scheme A)))
    (i n : ℕ) :
    cohomologyOnOpen M V i ⟶
      (Scheme.Hom.IdealPowerCohomology.Quotient.tower I (puncturedOpen A).ι M i).obj
        (op n) :=
  let additiveMap :=
    let Q := Scheme.Hom.IdealPowerCohomology.Quotient.stage I (puncturedOpen A).ι M n
    let toQuotient :=
      ((RingedSpace.moduleCohomologyAtOpenFunctor (scheme A).toRingedSpace V i) ⋙
        ModuleCat.restrictScalars (Scheme.Hom.sectionsMap (puncturedOpen A).ι V)).map
          (Scheme.Hom.IdealPowerCohomology.Quotient.projection I (puncturedOpen A).ι M n)
    (forget₂ (ModuleCat A) AddCommGrpCat).map toQuotient ≫
      eqToHom
        (Scheme.Modules.moduleCohomologyAtOpenForget_obj_eq_underlyingSheafCohomology V Q i) ≫
      TopCat.Sheaf.Cohomology.restrictionInverseOfSupport
        (((idealSheafDataOfIdealOnSpec I).comap (puncturedOpen A).ι).support.isClosed)
        ((SheafOfModules.toSheaf (scheme A).ringCatSheaf).obj Q)
        (quotientRestrictionToComplement_eq_zero I M n) i V hV ≫
      eqToHom (Scheme.Hom.cohomologyForget_obj_eq (puncturedOpen A).ι Q i).symm ≫
      (forget₂ (ModuleCat A) AddCommGrpCat).map
        (eqToHom (Scheme.Hom.IdealPowerCohomology.Quotient.tower_obj
          I (puncturedOpen A).ι M i n).symm)
  ModuleCat.homMk additiveMap (openCohomologyStageMap_smul I M V hV i n)

/-- The maps from open cohomology to quotient cohomology commute with the
successor transitions of the quotient tower. -/
theorem openCohomologyStageMap_naturality
    (I : Ideal A) (M : (scheme A).Modules) (V : (scheme A).Opens)
    (hV : (((idealSheafDataOfIdealOnSpec I).comap
      (puncturedOpen A).ι).support : Set (scheme A)) ⊆ (V : Set (scheme A)))
    (i n : ℕ) :
    ((Functor.const ℕᵒᵖ).obj (cohomologyOnOpen M V i)).map
          (homOfLE (Nat.le_add_right n 1)).op ≫
        openCohomologyStageMap I M V hV i n =
      openCohomologyStageMap I M V hV i (n + 1) ≫
        (Scheme.Hom.IdealPowerCohomology.Quotient.tower I (puncturedOpen A).ι M i).map
          (homOfLE (Nat.le_add_right n 1)).op := sorry

/-- The cone of quotient projections and supported extensions with vertex the
cohomology on an open containing the ideal support. -/
noncomputable def openCohomologyCone
    (I : Ideal A) (M : (scheme A).Modules) (V : (scheme A).Opens)
    (hV : (((idealSheafDataOfIdealOnSpec I).comap
      (puncturedOpen A).ι).support : Set (scheme A)) ⊆ (V : Set (scheme A)))
    (i : ℕ) :
    Cone (Scheme.Hom.IdealPowerCohomology.Quotient.tower I (puncturedOpen A).ι M i) where
  pt := cohomologyOnOpen M V i
  π := NatTrans.ofOpSequence (openCohomologyStageMap I M V hV i)
    (openCohomologyStageMap_naturality I M V hV i)

/-- The canonical comparison from cohomology on an open containing the ideal support
to the inverse limit of ideal-power quotient cohomology on the punctured spectrum. -/
noncomputable def openCohomologyComparison
    (I : Ideal A) (M : (scheme A).Modules) (V : (scheme A).Opens)
    (hV : (((idealSheafDataOfIdealOnSpec I).comap
      (puncturedOpen A).ι).support : Set (scheme A)) ⊆ (V : Set (scheme A)))
    (i : ℕ) :
    cohomologyOnOpen M V i ⟶
      limit (Scheme.Hom.IdealPowerCohomology.Quotient.tower I (puncturedOpen A).ι M i) :=
  limit.lift _ (openCohomologyCone I M V hV i)

/-- The component of the open-cohomology comparison at each quotient stage is the
quotient-and-supported-extension map. -/
theorem openCohomologyComparison_π
    (I : Ideal A) (M : (scheme A).Modules) (V : (scheme A).Opens)
    (hV : (((idealSheafDataOfIdealOnSpec I).comap
      (puncturedOpen A).ι).support : Set (scheme A)) ⊆ (V : Set (scheme A)))
    (i n : ℕ) :
    openCohomologyComparison I M V hV i ≫
        limit.π (Scheme.Hom.IdealPowerCohomology.Quotient.tower I (puncturedOpen A).ι M i)
          (op n) =
      openCohomologyStageMap I M V hV i n := sorry

/-- The open-cohomology comparison is independent of the proof that the open
contains the ideal support. -/
theorem openCohomologyComparison_proof_irrel
    (I : Ideal A) (M : (scheme A).Modules) (V : (scheme A).Opens)
    (hV hV' : (((idealSheafDataOfIdealOnSpec I).comap
      (puncturedOpen A).ι).support : Set (scheme A)) ⊆ (V : Set (scheme A)))
    (i : ℕ) :
    openCohomologyComparison I M V hV i = openCohomologyComparison I M V hV' i := sorry

end AlgebraicGeometry.PuncturedSpectrum
