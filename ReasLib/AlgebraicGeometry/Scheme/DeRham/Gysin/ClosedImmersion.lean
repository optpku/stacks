/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.DeRham.Gysin
public import ReasLib.AlgebraicGeometry.Scheme.Differentials.ExteriorPower.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.LocalCohomology.FundamentalClass
public import ReasLib.AlgebraicGeometry.Scheme.Differentials.Conormal
public import ReasLib.AlgebraicGeometry.Scheme.Differentials.Quasicoherent
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.AlgebraSheaf.Pullback
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.ExteriorPower.Sequence
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.ExteriorPower.DegreeZero
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.ExteriorPower.Properties
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.LocallyFree.Dualizable

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  Opposite RingedSpace RingedSpace.Hom Scheme.Hom SheafOfModules.RingedSite
open SheafOfModules.RingedSite.ExteriorAlgebra
  SheafOfModules.RingedSite.ExteriorPower
  Scheme.Hom.LocalCohomology
  Scheme.Hom.LocalCohomology.EquationPresentation
open scoped AlgebraicGeometry MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry
namespace Scheme.DeRham.Gysin

variable {Z X S : Scheme.{u}}

/-- Exterior-power relative differential forms on a scheme are quasicoherent. -/
theorem relativeFormIsQuasicoherent (f : X ⟶ S) (p : ℕ) :
    (sheaf X.𝒪 Ω[f.toShHom] p).IsQuasicoherent := sorry

/-- A relative differential-form sheaf, regarded as a quasicoherent scheme module. -/
abbrev relativeFormQCoh (f : X ⟶ S) (p : ℕ) : Scheme.QCoh X :=
  ⟨sheaf X.𝒪 Ω[f.toShHom] p, relativeFormIsQuasicoherent f p⟩

/-- Relative forms restricted to an open equation chart are canonically identified with the
relative forms of the restricted base morphism. -/
noncomputable def restrictedFormComparison {i : Z ⟶ X} [IsClosedImmersion i] {c : ℕ}
    (P : EquationPresentation i c) (f : X ⟶ S) (p : ℕ) :
    (Scheme.Modules.pullback P.carrier.ι).obj
        (sheaf X.𝒪 Ω[f.toShHom] p) ⟶
      sheaf P.carrier.toScheme.𝒪 Ω[(P.carrier.ι ≫ f).toShHom] p :=
  (Scheme.Modules.fromRingedSpace P.carrier.toScheme).map
    (Scheme.RelativeDifferentials.formComparison
      (CommSq.mk (Category.comp_id _).symm :
        CommSq P.carrier.ι (P.carrier.ι ≫ f) f (𝟙 S)) p)

/-- The relative-form comparison for an open equation chart is invertible. -/
theorem restrictedFormComparisonIsIso {i : Z ⟶ X} [IsClosedImmersion i] {c : ℕ}
    (P : EquationPresentation i c) (f : X ⟶ S) (p : ℕ) :
    IsIso (restrictedFormComparison P f p) := sorry

/-- The canonical isomorphism from restricted ambient forms to forms of the restricted base
morphism. -/
noncomputable def restrictedFormIso {i : Z ⟶ X} [IsClosedImmersion i] {c : ℕ}
    (P : EquationPresentation i c) (f : X ⟶ S) (p : ℕ) :
    P.coefficients (relativeFormQCoh f p) ≅
      sheaf P.carrier.toScheme.𝒪 Ω[(P.carrier.ι ≫ f).toShHom] p :=
  (Scheme.Modules.restrictFunctorIsoPullback P.carrier.ι).app _ ≪≫
    @asIso _ _ _ _ (restrictedFormComparison P f p)
      (restrictedFormComparisonIsIso P f p)

/-- The degreewise map from exterior powers after pullback to the pullback of exterior powers,
obtained from the canonical inverse comparison for the total exterior algebra. -/
noncomputable def pullbackFormComparisonInv (i : Z ⟶ X) (f : X ⟶ S) (p : ℕ) :
    sheaf Z.𝒪 ((RingedSpace.Hom.pullback i.toShHom).obj Ω[f.toShHom]) p ⟶
      (Scheme.Modules.pullback i).obj (sheaf X.𝒪 Ω[f.toShHom] p) :=
  (Scheme.Modules.fromRingedSpace Z).map
    (powerι Z.𝒪
        ((RingedSpace.Hom.pullback i.toShHom).obj Ω[f.toShHom]) p ≫
      ExteriorAlg.Pullback.comparisonInv i.toShHom Ω[f.toShHom] ≫
      (RingedSpace.Hom.pullback i.toShHom).map
        ((decompositionAppIso
          X.𝒪 Ω[f.toShHom]).hom ≫
          Limits.Sigma.π
            (gradedObject X.𝒪 Ω[f.toShHom]) p))

/-- Wedge a pulled-back ambient `p`-form on the right with the image of a top conormal form. -/
noncomputable def determinantWedgeForm (i : Z ⟶ X) (f : X ⟶ S) (c p : ℕ) :
    sheaf Z.𝒪 (Scheme.Hom.conormalSheaf i) c ⊗
        sheaf Z.𝒪 ((RingedSpace.Hom.pullback i.toShHom).obj Ω[f.toShHom]) p ⟶
      (Scheme.Modules.pullback i).obj (sheaf X.𝒪 Ω[f.toShHom] (p + c)) :=
  (β_ (sheaf Z.𝒪 (Scheme.Hom.conormalSheaf i) c)
      (sheaf Z.𝒪 ((RingedSpace.Hom.pullback i.toShHom).obj Ω[f.toShHom]) p)).hom ≫
    (𝟙 _ ⊗ₘ ExteriorPower.map Z.𝒪 (Conormal.Differentials.map i f) c) ≫
    mul Z.𝒪
      ((RingedSpace.Hom.pullback i.toShHom).obj Ω[f.toShHom]) p c ≫
    pullbackFormComparisonInv i f (p + c)

/-- Wedge multiplication by a top conormal form kills the relations defining the next
exterior power of `Ω_{Z/S}`. -/
theorem determinantWedgeForm_relation (i : Z ⟶ X) [IsClosedImmersion i]
    (f : X ⟶ S) (c p : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank c (Scheme.Hom.conormalSheaf i)] :
    (sequence Z.𝒪 (Conormal.Differentials.complex i f) p).f ≫
      MonoidalClosed.curry (determinantWedgeForm i f c (p + 1)) = 0 := sorry

/-- The exterior-power conormal sequence has an epimorphic final arrow. -/
theorem conormalExteriorSequenceEpi (i : Z ⟶ X) [IsClosedImmersion i]
    (f : X ⟶ S) (p : ℕ) :
    Epi (sequence Z.𝒪 (Conormal.Differentials.complex i f) p).g := sorry

/-- The exterior-power conormal sequence is exact. -/
theorem conormalExteriorSequenceExact (i : Z ⟶ X) [IsClosedImmersion i]
    (f : X ⟶ S) (p : ℕ) :
    (sequence Z.𝒪 (Conormal.Differentials.complex i f) p).Exact := sorry

/-- The canonical map from relative forms on `Z` to the internal Hom from the conormal
determinant into pulled-back ambient relative forms. -/
noncomputable def formToInternalHom (i : Z ⟶ X) [IsClosedImmersion i]
    (f : X ⟶ S) (c : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank c (Scheme.Hom.conormalSheaf i)] :
    (p : ℕ) → sheaf Z.𝒪 Ω[(i ≫ f).toShHom] p ⟶
      (ihom (sheaf Z.𝒪 (Scheme.Hom.conormalSheaf i) c)).obj
        ((Scheme.Modules.pullback i).obj (sheaf X.𝒪 Ω[f.toShHom] (p + c)))
  | 0 =>
      degreeZero Z.𝒪 Ω[(i ≫ f).toShHom] ≫
        one Z.𝒪
          ((RingedSpace.Hom.pullback i.toShHom).obj Ω[f.toShHom]) ≫
        MonoidalClosed.curry (determinantWedgeForm i f c 0)
  | p + 1 =>
      @ShortComplex.Exact.desc _ _ _
          (sequence Z.𝒪 (Conormal.Differentials.complex i f) p) _
          (conormalExteriorSequenceExact i f p) _
          (MonoidalClosed.curry (determinantWedgeForm i f c (p + 1)))
          (determinantWedgeForm_relation i f c p)
          (conormalExteriorSequenceEpi i f p)

/-- The tensor/internal-Hom comparison for the conormal determinant is invertible. -/
theorem determinantTensorComparisonIsIso (i : Z ⟶ X) (c : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank c (Scheme.Hom.conormalSheaf i)]
    (M : Z.Modules) :
    IsIso (MonoidalClosed.Dual.tensorComparison
      (sheaf Z.𝒪 (Scheme.Hom.conormalSheaf i) c) M) := sorry

/-- The canonical conormal-duality map from relative forms on `Z` to the source object of the
fundamental-class transformation. -/
noncomputable def formToFundamentalSource (i : Z ⟶ X) [IsClosedImmersion i]
    (f : X ⟶ S) (c p : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank c (Scheme.Hom.conormalSheaf i)] :
    sheaf Z.𝒪 Ω[(i ≫ f).toShHom] p ⟶
      (ihom (sheaf Z.𝒪 (Scheme.Hom.conormalSheaf i) c)).obj
        (SheafOfModules.unit Z.ringCatSheaf) ⊗
        (Scheme.Modules.pullback i).obj (sheaf X.𝒪 Ω[f.toShHom] (p + c)) :=
  formToInternalHom i f c p ≫
    @CategoryTheory.inv _ _ _ _
      (MonoidalClosed.Dual.tensorComparison
        (sheaf Z.𝒪 (Scheme.Hom.conormalSheaf i) c)
        ((Scheme.Modules.pullback i).obj (sheaf X.𝒪 Ω[f.toShHom] (p + c))))
      (determinantTensorComparisonIsIso i c
        ((Scheme.Modules.pullback i).obj (sheaf X.𝒪 Ω[f.toShHom] (p + c)))) ≫
    MonoidalCategoryStruct.whiskerLeft
      ((Scheme.Modules.pullback i).obj (sheaf X.𝒪 Ω[f.toShHom] (p + c)))
      ((ihom (sheaf Z.𝒪 (Scheme.Hom.conormalSheaf i) c)).map
        ((RingedSpace.unitIsoTensorUnit Z.toRingedSpace).symm.hom)) ≫
    (β_ ((Scheme.Modules.pullback i).obj (sheaf X.𝒪 Ω[f.toShHom] (p + c)))
      ((ihom (sheaf Z.𝒪 (Scheme.Hom.conormalSheaf i) c)).obj
        (SheafOfModules.unit Z.ringCatSheaf))).hom

/-- Pushforward of the conormal-duality map into the source of the fundamental-class
transformation. -/
noncomputable def toFundamentalSource (i : Z ⟶ X) [IsClosedImmersion i]
    (f : X ⟶ S) (c p : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank c (Scheme.Hom.conormalSheaf i)] :
    (Scheme.Modules.toRingedSpace X).obj
        ((Scheme.Modules.pushforward i).obj (sheaf Z.𝒪 Ω[(i ≫ f).toShHom] p)) ⟶
      (sourceFunctor i c).obj
        (relativeFormQCoh f (p + c)) :=
  (Scheme.Modules.toRingedSpace X).map
    ((Scheme.Modules.pushforward i).map (formToFundamentalSource i f c p))

/-- The degreewise canonical comparison from the pullback of ambient forms to the exterior
powers of the pulled-back relative differential module. -/
noncomputable def pullbackFormComparison (i : Z ⟶ X) (f : X ⟶ S) (p : ℕ) :
    (Scheme.Modules.pullback i).obj (sheaf X.𝒪 Ω[f.toShHom] p) ⟶
      sheaf Z.𝒪 ((RingedSpace.Hom.pullback i.toShHom).obj Ω[f.toShHom]) p :=
  (Scheme.Modules.pullback i).map
      (Limits.Sigma.ι (gradedObject X.𝒪 Ω[f.toShHom]) p) ≫
    (Scheme.Modules.pullback i).map
      ((decompositionAppIso X.𝒪 Ω[f.toShHom]).inv) ≫
    ExteriorAlg.Pullback.comparison i.toShHom Ω[f.toShHom] ≫
    (decompositionAppIso Z.𝒪
      ((RingedSpace.Hom.pullback i.toShHom).obj Ω[f.toShHom])).hom ≫
    Limits.Sigma.π
      (gradedObject Z.𝒪
        ((RingedSpace.Hom.pullback i.toShHom).obj Ω[f.toShHom])) p

/-- The canonical map from pulled-back ambient forms to relative forms on the closed
subscheme. -/
noncomputable def pullbackFormToClosedForm (i : Z ⟶ X) (f : X ⟶ S) :
    (p : ℕ) → (Scheme.Modules.pullback i).obj (sheaf X.𝒪 Ω[f.toShHom] p) ⟶
      sheaf Z.𝒪 Ω[(i ≫ f).toShHom] p
  | 0 =>
      pullbackFormComparison i f 0 ≫
        degreeZero Z.𝒪 ((RingedSpace.Hom.pullback i.toShHom).obj Ω[f.toShHom]) ≫
        (degreeZeroIso Z.𝒪 Ω[(i ≫ f).toShHom]).inv
  | p + 1 =>
      pullbackFormComparison i f (p + 1) ≫
        (sequence Z.𝒪 (Conormal.Differentials.complex i f) p).g

/-- The presented algebraic form maps to its standard exterior-power realization. -/
noncomputable def algebraicFormToExterior {A B : CommRingCat.{u}} (g : A ⟶ B) (p : ℕ) :
    CommRingCat.DeRham.form g p ⟶
      (CommRingCat.KaehlerDifferential g).exteriorPower p :=
  -- Local instance justification (defeq pin): both comparisons must use the algebra structure canonically induced by `g`.
  letI := g.hom.toAlgebra
  match p with
  | 0 =>
      KaehlerDifferential.DeRham.toExterior A B 0 ≫
        (ModuleCat.exteriorPower.iso₀ (CommRingCat.KaehlerDifferential g)).inv
  | 1 =>
      KaehlerDifferential.DeRham.toExterior A B 1 ≫
        (ModuleCat.exteriorPower.iso₁ (CommRingCat.KaehlerDifferential g)).inv
  | p + 2 => KaehlerDifferential.DeRham.toExterior A B (p + 2)

/-- The sectionwise presented-form evaluation is natural under restriction. -/
theorem presentedFormToExteriorApp_naturality (f : X ⟶ S) (p : ℕ)
    {U V : X.Opensᵒᵖ} (r : U ⟶ V) :
    (PresheafOfModules.DeRham.form
          (RingedSpace.DeRham.structureMap f.toLRSHom.toShHom).hom p).map r ≫
        (ModuleCat.restrictScalars (X.𝒪.obj.map r).hom).map
          (algebraicFormToExterior
            ((RingedSpace.DeRham.structureMap f.toLRSHom.toShHom).hom.app V) p) =
      (algebraicFormToExterior
          ((RingedSpace.DeRham.structureMap f.toLRSHom.toShHom).hom.app U) p) ≫
        (PresheafOfModules.ExteriorPower.presheaf X.𝒪.obj
          (PresheafOfModules.DifferentialsConstruction.relativeDifferentials'
            (RingedSpace.DeRham.structureMap f.toLRSHom.toShHom).hom) p).map r := sorry

/-- The canonical presheaf map from presented relative forms to exterior powers of the
sectionwise relative-differential modules. -/
noncomputable def presentedFormToExteriorPresheaf (f : X ⟶ S) (p : ℕ) :
    PresheafOfModules.DeRham.form
        (RingedSpace.DeRham.structureMap f.toLRSHom.toShHom).hom p ⟶
      PresheafOfModules.ExteriorPower.presheaf X.𝒪.obj
        (PresheafOfModules.DifferentialsConstruction.relativeDifferentials'
          (RingedSpace.DeRham.structureMap f.toLRSHom.toShHom).hom) p where
  app U := algebraicFormToExterior
    ((RingedSpace.DeRham.structureMap f.toLRSHom.toShHom).hom.app U) p
  naturality r := presentedFormToExteriorApp_naturality f p r

/-- The canonical presheaf map from presented relative forms to the exterior powers of the
sheafified relative-differential module. -/
noncomputable def formToExteriorPresheaf (f : X ⟶ S) (p : ℕ) :
    PresheafOfModules.DeRham.form
        (RingedSpace.DeRham.structureMap f.toLRSHom.toShHom).hom p ⟶
      PresheafOfModules.ExteriorPower.presheaf X.𝒪.obj Ω[f.toShHom].val p :=
  presentedFormToExteriorPresheaf f p ≫
    PresheafOfModules.ExteriorPower.hom X.𝒪.obj
      (moduleSheafificationUnitToVal X.𝒪
        (PresheafOfModules.DifferentialsConstruction.relativeDifferentials'
          (RingedSpace.DeRham.structureMap f.toLRSHom.toShHom).hom)) p

/-- The canonical sheafified comparison from presented relative forms to exterior powers of
the relative-differential sheaf. -/
noncomputable def formToExterior (f : X ⟶ S) (p : ℕ) :
    RingedSpace.DeRham.form f.toLRSHom.toShHom p ⟶
      sheaf X.𝒪 Ω[f.toShHom] p :=
  (moduleSheafification X.𝒪).map (formToExteriorPresheaf f p)

/-- The presented-form comparison with the exterior-power model is invertible. -/
theorem formToExteriorIsIso (f : X ⟶ S) (p : ℕ) :
    IsIso (formToExterior f p) := sorry

/-- The canonical degree-`p` Gysin morphism for a finitely presented closed immersion whose
conormal sheaf is locally free of rank `c`. -/
noncomputable def mapOfClosedImmersion (i : Z ⟶ X) [IsClosedImmersion i]
    [Scheme.Hom.FinitePresentation i] (f : X ⟶ S) (c p : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank c (Scheme.Hom.conormalSheaf i)] :
    (Scheme.Modules.toRingedSpace X).obj
        ((Scheme.Modules.pushforward i).obj (sheaf Z.𝒪 Ω[(i ≫ f).toShHom] p)) ⟶
      (functor i c).obj (relativeFormQCoh f (p + c)) :=
  toFundamentalSource i f c p ≫
    (fundamentalClass i c).app
      (relativeFormQCoh f (p + c))

/-- The equation-map relative forms are canonically identified with the exterior-power sheaves
used by the global construction. -/
noncomputable def equationRelativeFormIso {i : Z ⟶ X} [IsClosedImmersion i] {c : ℕ}
    (P : EquationPresentation i c)
    (f : X ⟶ S) (p : ℕ) :
    relativeForm (P.carrier.ι ≫ f) p ≅
      sheaf P.carrier.toScheme.𝒪 Ω[(P.carrier.ι ≫ f).toShHom] p :=
  eqToIso (Scheme.Modules.fromRingedSpace_obj
      (RingedSpace.DeRham.form (P.carrier.ι ≫ f).toLRSHom.toShHom p)) ≪≫
    @asIso _ _ _ _ (formToExterior (P.carrier.ι ≫ f) p)
      (formToExteriorIsIso (P.carrier.ι ≫ f) p)

/-- The source comparison on an equation chart restricts pulled-back ambient forms, identifies
the restricted forms with those for `P.carrier.ι ≫ f`, and passes to the equation presentation
of `Ω^p`. -/
noncomputable def equationGysinSourceComparison (i : Z ⟶ X) [IsClosedImmersion i]
    (f : X ⟶ S) (c p : ℕ) (P : EquationPresentation i c) :
    ((Scheme.Modules.pushforward i).obj
        ((Scheme.Modules.pullback i).obj (sheaf X.𝒪 Ω[f.toShHom] p))).val.presheaf.obj
          (op P.carrier) ⟶
      (source (P.carrier.ι ≫ f) P.generators p).val.presheaf.obj (op ⊤) :=
  let M := (Scheme.Modules.pullback i).obj (sheaf X.𝒪 Ω[f.toShHom] p)
  let N := (Scheme.Modules.pushforward i).obj M
  AddCommGrpCat.ofHom
      (N.val.map
        (eqToHom (P.carrier.ι.image_top_eq_opensRange.trans
          (Scheme.Opens.opensRange_ι P.carrier))).op).hom.toAddMonoidHom ≫
    AddCommGrpCat.ofHom
      (Scheme.Modules.restrictAppIso P.carrier.ι N ⊤).inv.hom ≫
    AddCommGrpCat.ofHom
      (((Scheme.Modules.restrictFunctorIsoPullback P.carrier.ι).hom.app N).val.app
        (op ⊤)).hom.toAddMonoidHom ≫
    AddCommGrpCat.ofHom
      ((((BaseChange.map (restrictionSquare P)).app M ≫
        (Scheme.Modules.pushforward P.restrictedImmersion).map
          (coefficientBaseChange P (relativeFormQCoh f p))).val.app
            (op ⊤)).hom.toAddMonoidHom) ≫
    coefficientComparison P (relativeFormQCoh f p) ≫
    (forget₂ _ _).map
      (((ModuleCech.LocalCohomology.zeroLocusPullback P.generators).map
        ((restrictedFormIso P f p).hom ≫
          (equationRelativeFormIso P f p).inv)).val.app (op ⊤)) ≫
    (forget₂ _ _).map
      ((projection (P.carrier.ι ≫ f) P.generators p).val.app (op ⊤))

/-- The target comparison from the local equation Gysin target to the component of global
cohomology with support on the equation chart. -/
noncomputable def equationGysinTargetComparison (i : Z ⟶ X) [IsClosedImmersion i]
    (f : X ⟶ S) (c p : ℕ) [Scheme.Hom.FinitePresentation i]
    [SheafOfModules.IsFiniteLocallyFreeOfRank c (Scheme.Hom.conormalSheaf i)]
    (P : EquationPresentation i c) :
    ((ModuleCech.LocalCohomology.cohomologyFunctor P.generators).obj
        (relativeForm (P.carrier.ι ≫ f) p)).val.presheaf.obj (op ⊤) ⟶
      ((functor i c).obj (relativeFormQCoh f p)).val.presheaf.obj (op P.carrier) :=
  (forget₂ _ _).map
      (((ModuleCech.LocalCohomology.cohomologyFunctor P.generators).map
        ((equationRelativeFormIso P f p).hom ≫
          (restrictedFormIso P f p).inv)).val.app (op ⊤)) ≫
    targetComparison P (relativeFormQCoh f p)

/-- On an affine equation presentation, the canonical closed-immersion Gysin morphism agrees,
after the canonical source and target comparisons, with the Gysin morphism determined by the
ordered equations. -/
theorem mapOfClosedImmersion_ofPresentation (i : Z ⟶ X) [IsClosedImmersion i]
    [Scheme.Hom.FinitePresentation i] (f : X ⟶ S) (c p : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank c (Scheme.Hom.conormalSheaf i)]
    (P : EquationPresentation i c) :
    (forget₂ _ _).map
          (((Scheme.Modules.pushforward i).map
            (pullbackFormToClosedForm i f p)).val.app (op P.carrier)) ≫
        (forget₂ _ _).map
          ((mapOfClosedImmersion i f c p).val.app (op P.carrier)) =
      equationGysinSourceComparison i f c p P ≫
        (forget₂ _ _).map
          ((map (P.carrier.ι ≫ f) P.generators p).val.app (op ⊤)) ≫
        equationGysinTargetComparison i f c (p + c) P := sorry

end Scheme.DeRham.Gysin
end AlgebraicGeometry

end
