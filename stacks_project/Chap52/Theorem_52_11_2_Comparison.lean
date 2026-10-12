/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap52.Lemma_52_7_3
public import ReasLib.AlgebraicGeometry.PuncturedSpectrum

/-!
# Cohomology comparison on punctured-spectrum neighborhoods

This file constructs the canonical map from cohomology on an open neighborhood of the
ideal-theoretic closed subset to the inverse limit of the positive ideal-power quotient
cohomology system.
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

/-- The positive `I`-power quotient of a module on the punctured spectrum at exponent
`n + 1`, viewed in the scheme-module category. -/
noncomputable abbrev positiveQuotient (I : Ideal A) (M : (scheme A).Modules) (n : ℕ) :
    (scheme A).Modules :=
  (Scheme.Modules.fromRingedSpace (scheme A)).obj
    ((PowerQuotientModule.system.{u, u, u}
      (((idealSheafDataOfIdealOnSpec I).comap (puncturedOpen A).ι).toSubobject)
      ((Scheme.Modules.toRingedSpace (scheme A)).obj M)).obj (op (n + 1)))

/-- The canonical projection of a module on the punctured spectrum to its positive
`I`-power quotient at exponent `n + 1`. -/
noncomputable abbrev positiveQuotientProjection
    (I : Ideal A) (M : (scheme A).Modules) (n : ℕ) :
    M ⟶ positiveQuotient I M n :=
  (Scheme.Modules.fromRingedSpace (scheme A)).map
    (PowerQuotientModule.projection
      (((idealSheafDataOfIdealOnSpec I).comap (puncturedOpen A).ι).toSubobject)
      ((Scheme.Modules.toRingedSpace (scheme A)).obj M) (n + 1))

/-- Degree-`i` cohomology of `M` on a punctured-spectrum neighborhood `V`, represented
canonically by cohomology of the direct image of `M|_V`. -/
noncomputable abbrev neighborhoodCohomology
    (I : Ideal A) (M : (scheme A).Modules) (V : (scheme A).Opens) (i : ℕ) :
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
        (positiveQuotient I M n)).val.app W).hom := sorry

/-- The inverse function of a bijective linear map preserves addition. -/
theorem positiveQuotientUnitInverse_add {R : Type u} [Ring R]
    {P Q : ModuleCat.{u} R} (f : P ⟶ Q) (hf : Function.Bijective f)
    (x y : Q) :
    Function.invFun f (x + y) = Function.invFun f x + Function.invFun f y := sorry

/-- The inverse function of a bijective linear map preserves scalar multiplication. -/
theorem positiveQuotientUnitInverse_smul {R : Type u} [Ring R]
    {P Q : ModuleCat.{u} R} (f : P ⟶ Q) (hf : Function.Bijective f)
    (r : R) (x : Q) :
    Function.invFun f (r • x) = r • Function.invFun f x := sorry

/-- The objectwise extension of sections of a positive quotient from a neighborhood containing
its support. Its underlying function is the canonical inverse function of restriction. -/
noncomputable def positiveQuotientUnitInverseApp
    (I : Ideal A) (M : (scheme A).Modules) (V : (scheme A).Opens)
    (hV : (((idealSheafDataOfIdealOnSpec I).comap
      (puncturedOpen A).ι).support : Set (scheme A)) ⊆ (V : Set (scheme A)))
    (n : ℕ) (W : ((scheme A).Opens)ᵒᵖ) :
    ((Scheme.Modules.pushforward V.ι).obj
        ((Scheme.Modules.pullback V.ι).obj (positiveQuotient I M n))).val.obj W ⟶
      (positiveQuotient I M n).val.obj W :=
  let inverseOfBijective := fun {R : Type u} [Ring R]
      {P Q : ModuleCat.{u} R} (f : P ⟶ Q) (hf : Function.Bijective f) ↦
    ModuleCat.ofHom
      { toFun := Function.invFun f
        map_add' := positiveQuotientUnitInverse_add f hf
        map_smul' := positiveQuotientUnitInverse_smul f hf }
  inverseOfBijective
    (((Scheme.Modules.pullbackPushforwardAdjunction V.ι).unit.app
      (positiveQuotient I M n)).val.app W)
    (positiveQuotientUnitApp_bijective I M V hV n W)

/-- Objectwise supported-section extension is the inverse-function construction applied to the
restriction map. -/
theorem positiveQuotientUnitInverseApp_apply
    (I : Ideal A) (M : (scheme A).Modules) (V : (scheme A).Opens)
    (hV : (((idealSheafDataOfIdealOnSpec I).comap
      (puncturedOpen A).ι).support : Set (scheme A)) ⊆ (V : Set (scheme A)))
    (n : ℕ) (W : ((scheme A).Opens)ᵒᵖ)
    (x : ((Scheme.Modules.pushforward V.ι).obj
      ((Scheme.Modules.pullback V.ι).obj (positiveQuotient I M n))).val.obj W) :
    positiveQuotientUnitInverseApp I M V hV n W x =
      Function.invFun
        (((Scheme.Modules.pullbackPushforwardAdjunction V.ι).unit.app
          (positiveQuotient I M n)).val.app W).hom x := sorry

/-- The objectwise supported-section extensions commute with restriction maps. -/
theorem positiveQuotientUnitInverseApp_naturality
    (I : Ideal A) (M : (scheme A).Modules) (V : (scheme A).Opens)
    (hV : (((idealSheafDataOfIdealOnSpec I).comap
      (puncturedOpen A).ι).support : Set (scheme A)) ⊆ (V : Set (scheme A)))
    (n : ℕ) {W W' : ((scheme A).Opens)ᵒᵖ} (f : W ⟶ W') :
    ((Scheme.Modules.pushforward V.ι).obj
        ((Scheme.Modules.pullback V.ι).obj (positiveQuotient I M n))).val.map f ≫
        (ModuleCat.restrictScalars ((scheme A).ringCatSheaf.obj.map f).hom).map
          (positiveQuotientUnitInverseApp I M V hV n W') =
      positiveQuotientUnitInverseApp I M V hV n W ≫
        (positiveQuotient I M n).val.map f := sorry

/-- The explicit extension-by-support morphism from the direct image of the restricted positive
quotient back to the positive quotient on the punctured spectrum. -/
noncomputable def positiveQuotientUnitInverse
    (I : Ideal A) (M : (scheme A).Modules) (V : (scheme A).Opens)
    (hV : (((idealSheafDataOfIdealOnSpec I).comap
      (puncturedOpen A).ι).support : Set (scheme A)) ⊆ (V : Set (scheme A)))
    (n : ℕ) :
    (Scheme.Modules.pushforward V.ι).obj
        ((Scheme.Modules.pullback V.ι).obj (positiveQuotient I M n)) ⟶
      positiveQuotient I M n :=
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
        (positiveQuotient I M n) ≫ positiveQuotientUnitInverse I M V hV n =
      𝟙 (positiveQuotient I M n) := sorry

/-- Explicit supported-section extension followed by restriction is the identity on the direct
image of the restricted positive quotient. -/
theorem positiveQuotientInverse_comp_unit
    (I : Ideal A) (M : (scheme A).Modules) (V : (scheme A).Opens)
    (hV : (((idealSheafDataOfIdealOnSpec I).comap
      (puncturedOpen A).ι).support : Set (scheme A)) ⊆ (V : Set (scheme A)))
    (n : ℕ) :
    positiveQuotientUnitInverse I M V hV n ≫
        (Scheme.Modules.pullbackPushforwardAdjunction V.ι).unit.app
          (positiveQuotient I M n) =
      𝟙 ((Scheme.Modules.pushforward V.ι).obj
        ((Scheme.Modules.pullback V.ι).obj (positiveQuotient I M n))) := sorry

/-- The restriction unit for a positive quotient, with its inverse given by explicit
supported-section extension. -/
noncomputable def positiveQuotientUnitIso
    (I : Ideal A) (M : (scheme A).Modules) (V : (scheme A).Opens)
    (hV : (((idealSheafDataOfIdealOnSpec I).comap
      (puncturedOpen A).ι).support : Set (scheme A)) ⊆ (V : Set (scheme A)))
    (n : ℕ) :
    positiveQuotient I M n ≅
      (Scheme.Modules.pushforward V.ι).obj
        ((Scheme.Modules.pullback V.ι).obj (positiveQuotient I M n)) where
  hom := (Scheme.Modules.pullbackPushforwardAdjunction V.ι).unit.app
    (positiveQuotient I M n)
  inv := positiveQuotientUnitInverse I M V hV n
  hom_inv_id := positiveQuotientUnit_comp_inverse I M V hV n
  inv_hom_id := positiveQuotientInverse_comp_unit I M V hV n

/-- The canonical extension from cohomology of the quotient on `V` to the corresponding
positive quotient-cohomology stage on the punctured spectrum. -/
noncomputable def quotientCohomologyExtension
    (I : Ideal A) (M : (scheme A).Modules) (V : (scheme A).Opens)
    (hV : (((idealSheafDataOfIdealOnSpec I).comap
      (puncturedOpen A).ι).support : Set (scheme A)) ⊆ (V : Set (scheme A)))
    (i n : ℕ) :
    neighborhoodCohomology I (positiveQuotient I M n) V i ⟶
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
              (positiveQuotient I M n)) =
      𝟙 (neighborhoodCohomology I (positiveQuotient I M n) V i) := sorry

/-- The map from neighborhood cohomology to the `n`th positive quotient-cohomology
stage: first take the quotient on `V`, then extend from its support. -/
noncomputable def cohomologyProjection
    (I : Ideal A) (M : (scheme A).Modules) (V : (scheme A).Opens)
    (hV : (((idealSheafDataOfIdealOnSpec I).comap
      (puncturedOpen A).ι).support : Set (scheme A)) ⊆ (V : Set (scheme A)))
    (i n : ℕ) :
    neighborhoodCohomology I M V i ⟶
      (quotientCohomologySystem (puncturedOpen A).ι I M (i : ℤ)).obj (op n) :=
  (ModuleCech.moduleToDerived (scheme A) ⋙
      Scheme.FlatPullbackSections.baseSections (puncturedOpen A).ι ⋙
      DerivedCategory.homologyFunctor (ModuleCat.{u} A) (i : ℤ)).map
        ((Scheme.Modules.pushforward V.ι).map
          ((Scheme.Modules.pullback V.ι).map (positiveQuotientProjection I M n))) ≫
    quotientCohomologyExtension I M V hV i n

/-- The neighborhood cohomology projections commute with the transitions of the positive
quotient-cohomology system. -/
theorem cohomologyProjection_naturality
    (I : Ideal A) (M : (scheme A).Modules) (V : (scheme A).Opens)
    (hV : (((idealSheafDataOfIdealOnSpec I).comap
      (puncturedOpen A).ι).support : Set (scheme A)) ⊆ (V : Set (scheme A)))
    (i n : ℕ) :
    ((Functor.const ℕᵒᵖ).obj (neighborhoodCohomology I M V i)).map
          (homOfLE (Nat.le_add_right n 1)).op ≫
        cohomologyProjection I M V hV i n =
      cohomologyProjection I M V hV i (n + 1) ≫
        (quotientCohomologySystem (puncturedOpen A).ι I M (i : ℤ)).map
          (homOfLE (Nat.le_add_right n 1)).op := sorry

/-- The explicit cone from neighborhood cohomology to the positive quotient-cohomology
system. -/
noncomputable def cohomologyCone
    (I : Ideal A) (M : (scheme A).Modules) (V : (scheme A).Opens)
    (hV : (((idealSheafDataOfIdealOnSpec I).comap
      (puncturedOpen A).ι).support : Set (scheme A)) ⊆ (V : Set (scheme A)))
    (i : ℕ) :
    Cone (quotientCohomologySystem (puncturedOpen A).ι I M (i : ℤ)) where
  pt := neighborhoodCohomology I M V i
  π := NatTrans.ofOpSequence (cohomologyProjection I M V hV i)
    (cohomologyProjection_naturality I M V hV i)

/-- The canonical morphism from degree-`i` cohomology on `V` to the inverse limit of
cohomology of the positive `I`-power quotients on the punctured spectrum. -/
noncomputable def cohomologyComparison
    (I : Ideal A) (M : (scheme A).Modules) (V : (scheme A).Opens)
    (hV : (((idealSheafDataOfIdealOnSpec I).comap
      (puncturedOpen A).ι).support : Set (scheme A)) ⊆ (V : Set (scheme A)))
    (i : ℕ) :
    neighborhoodCohomology I M V i ⟶
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

end AlgebraicGeometry.PuncturedSpectrum
