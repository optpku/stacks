module

public import ReasLib.AlgebraicGeometry.PuncturedSpectrum.CohomologyStabilization
public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Completion.Neighborhood
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.Homology
public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints
public import ReasLib.AlgebraicGeometry.Scheme.Module.Sections
public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.CohomologicalDimension

public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.PuncturedSpectrum

open Scheme Scheme.Modules Scheme.ModuleDerived.DerivedCompletion
  RingedSpace.Module.Derived

/-- The canonical identification of a module placed in degree zero with the
nonnegative-complex realization used by `ModuleCech.moduleToDerived`. -/
private noncomputable def singleIsoModuleToDerived
    (A : Type u) [CommRing A] [IsLocalRing A] (M : (scheme A).Modules) :
    (DerivedCategory.singleFunctor (scheme A).toRingedSpace.Modules 0).obj
        ((Scheme.Modules.toRingedSpace (scheme A)).obj M) ≅
      (ModuleCech.moduleToDerived (scheme A)).obj M :=
  let G := Scheme.Modules.toRingedSpace (scheme A)
  let e :
      ((((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj
          ((CochainComplex.single₀ (scheme A).Modules).obj M)).extend
            ComplexShape.embeddingUpNat) :
        CochainComplex (scheme A).toRingedSpace.Modules ℤ) ≅
        (CochainComplex.singleFunctor (scheme A).toRingedSpace.Modules 0).obj
          (G.obj M) :=
    (ComplexShape.embeddingUpNat.extendFunctor
        (scheme A).toRingedSpace.Modules).mapIso
          ((HomologicalComplex.singleMapHomologicalComplex G
            (ComplexShape.up ℕ) 0).app M) ≪≫
      HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat
        (G.obj M) 0 0 rfl
  (DerivedCategory.Q.mapIso e).symm

/-- The canonical map from ordinary global sections on the punctured spectrum
to degree-zero derived global sections over `A`. -/
private noncomputable def sectionsToCohomologyZero
    (A : Type u) [CommRing A] [IsLocalRing A] (M : (scheme A).Modules) :
    ((ModuleCat.restrictScalars
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv).hom).obj
      ((ModuleCat.restrictScalars (puncturedOpen A).ι.appTop.hom).obj
        ((RingedSpace.moduleGlobalSectionsFunctor
          (scheme A).toRingedSpace).obj
            ((Scheme.Modules.toRingedSpace (scheme A)).obj M)))) ⟶
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj
        ((Scheme.FlatPullbackSections.baseSections (puncturedOpen A).ι).obj
          ((ModuleCech.moduleToDerived (scheme A)).obj M)) :=
  let X := scheme A
  let G := RingedSpace.moduleGlobalSectionsFunctor X.toRingedSpace
  let N := (Scheme.Modules.toRingedSpace X).obj M
  let K := (CochainComplex.singleFunctor X.toRingedSpace.Modules 0).obj N
  let L := (GlobalSections.functor X.toRingedSpace).obj
    ((ModuleCech.moduleToDerived X).obj M)
  let comparison :
      (DerivedCategory.singleFunctor (ModuleCat.{u}
        (RingedSpace.globalSectionsRing X.toRingedSpace)) 0).obj (G.obj N) ⟶ L :=
    (DerivedCategory.singleFunctorIsoCompQ
        (ModuleCat.{u} (RingedSpace.globalSectionsRing X.toRingedSpace)) 0).hom.app _ ≫
      DerivedCategory.Q.map
        ((HomologicalComplex.singleMapHomologicalComplex G
          (ComplexShape.up ℤ) 0).inv.app N) ≫
      (GlobalSections.unit X.toRingedSpace).app K ≫
      (GlobalSections.functor X.toRingedSpace).map
        (singleIsoModuleToDerived A M).hom
  let comparisonZero : G.obj N ⟶
      (DerivedCategory.homologyFunctor
        (ModuleCat.{u} (RingedSpace.globalSectionsRing X.toRingedSpace)) 0).obj L :=
    (DerivedCategory.singleFunctorCompHomologyFunctorIso
        (ModuleCat.{u} (RingedSpace.globalSectionsRing X.toRingedSpace)) 0).inv.app _ ≫
      (DerivedCategory.homologyFunctor
        (ModuleCat.{u} (RingedSpace.globalSectionsRing X.toRingedSpace)) 0).map comparison
  let firstRestriction :=
    (ModuleCat.restrictScalars (puncturedOpen A).ι.appTop.hom).map comparisonZero ≫
      (ModuleCat.derivedRestrictionHomologyIso
        (puncturedOpen A).ι.appTop.hom L 0).inv
  (ModuleCat.restrictScalars
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv).hom).map firstRestriction ≫
    (ModuleCat.derivedRestrictionHomologyIso
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv).hom
      ((ModuleCat.derivedRestrictionOfScalars
        (puncturedOpen A).ι.appTop.hom).obj L) 0).inv

/-- The canonical map from ordinary sections on one neighborhood of the ideal
support to degree-zero cohomology on that neighborhood. -/
private noncomputable def neighborhoodSectionToCohomologyZero
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (I : Ideal A) (M : (scheme A).Modules)
    (V : (Scheme.CoherentCompletion.compactSupport
      ((idealSheafDataOfIdealOnSpec I).comap (puncturedOpen A).ι)).openNhdsᵒᵖ) :
    (Scheme.CoherentCompletion.neighborhoodSectionsDiagram
        ((idealSheafDataOfIdealOnSpec I).comap (puncturedOpen A).ι) M).obj V →
      directImageCohomology M V.unop.1 0 :=
  fun s ↦
    let W := V.unop.1
    let j := Scheme.Opens.ι W
    let N := (Scheme.Modules.pullback j).obj M
    let sectionAtTop :
        N.val.obj (Opposite.op (⊤ : (Scheme.Opens.toScheme W).Opens)) :=
      Eq.mp (congrArg (fun W' ↦ (N.val.obj (Opposite.op W') : Type u))
        (Scheme.Opens.ι_preimage_self W))
          ((((Scheme.Modules.pullbackPushforwardAdjunction j).unit.app M).val.app
            (Opposite.op W)).hom s)
    sectionsToCohomologyZero A ((Scheme.Modules.pushforward j).obj N) sectionAtTop

/-- The canonical map from sections on one neighborhood to the degree-zero
quotient-cohomology limit. -/
noncomputable def neighborhoodSectionToQuotientCohomologyLimit
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (I : Ideal A) (M : (scheme A).Modules)
    (V : (Scheme.CoherentCompletion.compactSupport
      ((idealSheafDataOfIdealOnSpec I).comap (puncturedOpen A).ι)).openNhdsᵒᵖ) :
    (Scheme.CoherentCompletion.neighborhoodSectionsDiagram
        ((idealSheafDataOfIdealOnSpec I).comap (puncturedOpen A).ι) M).obj V ⟶
      ((limit (quotientCohomologySystem (puncturedOpen A).ι I M 0) :
        ModuleCat.{u} A) : Type u) :=
  ↾fun s ↦ cohomologyComparison I M V.unop.1 V.unop.2 0
    (neighborhoodSectionToCohomologyZero A I M V s)

/-- The neighborhood-to-quotient-cohomology maps commute with restriction of
ordinary sections between neighborhoods. -/
theorem neighborhoodSectionToQuotientCohomologyLimit_naturality
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (I : Ideal A) (M : (scheme A).Modules)
    {V W : (Scheme.CoherentCompletion.compactSupport
      ((idealSheafDataOfIdealOnSpec I).comap (puncturedOpen A).ι)).openNhdsᵒᵖ}
    (f : V ⟶ W) :
    (Scheme.CoherentCompletion.neighborhoodSectionsDiagram
          ((idealSheafDataOfIdealOnSpec I).comap (puncturedOpen A).ι) M).map f ≫
        neighborhoodSectionToQuotientCohomologyLimit A I M W =
      neighborhoodSectionToQuotientCohomologyLimit A I M V ≫
        ((Functor.const (Scheme.CoherentCompletion.compactSupport
          ((idealSheafDataOfIdealOnSpec I).comap
            (puncturedOpen A).ι)).openNhdsᵒᵖ).obj
              ((limit (quotientCohomologySystem (puncturedOpen A).ι I M 0) :
                ModuleCat.{u} A) : Type u)).map f := sorry

/-- Sections on a neighborhood of the pullback of `V(I)`, regarded as an `A`-module
through the structural morphism from the punctured spectrum to `Spec(A)`. -/
@[expose] noncomputable def neighborhoodSectionsModule
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (I : Ideal A) (M : (scheme A).Modules)
    (V : (Scheme.CoherentCompletion.compactSupport
      ((idealSheafDataOfIdealOnSpec I).comap (puncturedOpen A).ι)).openNhdsᵒᵖ) :
    ModuleCat.{u} A :=
  Scheme.Hom.sectionsModOverSpec (puncturedOpen A).ι V.unop.1 M

/-- The carrier of `neighborhoodSectionsModule` is the ordinary section type on the
underlying neighborhood. -/
theorem neighborhoodSectionsModule_carrier
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (I : Ideal A) (M : (scheme A).Modules)
    (V : (Scheme.CoherentCompletion.compactSupport
      ((idealSheafDataOfIdealOnSpec I).comap (puncturedOpen A).ι)).openNhdsᵒᵖ) :
    (neighborhoodSectionsModule A I M V : Type u) =
      (Scheme.CoherentCompletion.neighborhoodSectionsDiagram
        ((idealSheafDataOfIdealOnSpec I).comap (puncturedOpen A).ι) M).obj V := sorry

/-- Restriction of ordinary sections between neighborhoods, viewed on the carriers of
their canonical `A`-module structures. -/
@[expose] noncomputable def neighborhoodSectionRestrict
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (I : Ideal A) (M : (scheme A).Modules)
    {V W : (Scheme.CoherentCompletion.compactSupport
      ((idealSheafDataOfIdealOnSpec I).comap (puncturedOpen A).ι)).openNhdsᵒᵖ}
    (f : V ⟶ W) :
    neighborhoodSectionsModule A I M V → neighborhoodSectionsModule A I M W :=
  fun x ↦ (Scheme.CoherentCompletion.neighborhoodSectionsDiagram
    ((idealSheafDataOfIdealOnSpec I).comap (puncturedOpen A).ι) M).map f x

/-- The underlying function of `neighborhoodSectionRestrict` is restriction in the
ordinary neighborhood-section diagram. -/
theorem neighborhoodSectionRestrict_apply
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (I : Ideal A) (M : (scheme A).Modules)
    {V W : (Scheme.CoherentCompletion.compactSupport
      ((idealSheafDataOfIdealOnSpec I).comap (puncturedOpen A).ι)).openNhdsᵒᵖ}
    (f : V ⟶ W) (x : neighborhoodSectionsModule A I M V) :
    neighborhoodSectionRestrict A I M f x =
      (Scheme.CoherentCompletion.neighborhoodSectionsDiagram
        ((idealSheafDataOfIdealOnSpec I).comap (puncturedOpen A).ι) M).map f x := sorry

/-- Restriction of neighborhood sections preserves addition after all section modules
are regarded as `A`-modules through `Spec(A)`. -/
theorem neighborhoodSectionsMap_add
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (I : Ideal A) (M : (scheme A).Modules)
    {V W : (Scheme.CoherentCompletion.compactSupport
      ((idealSheafDataOfIdealOnSpec I).comap (puncturedOpen A).ι)).openNhdsᵒᵖ}
    (f : V ⟶ W)
    (x y : neighborhoodSectionsModule A I M V) :
    neighborhoodSectionRestrict A I M f (x + y) =
      neighborhoodSectionRestrict A I M f x +
        neighborhoodSectionRestrict A I M f y := sorry

/-- Restriction of neighborhood sections preserves the `A`-scalar action induced by
the structural maps from `A`. -/
theorem neighborhoodSectionsMap_smul
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (I : Ideal A) (M : (scheme A).Modules)
    {V W : (Scheme.CoherentCompletion.compactSupport
      ((idealSheafDataOfIdealOnSpec I).comap (puncturedOpen A).ι)).openNhdsᵒᵖ}
    (f : V ⟶ W) (a : A)
    (x : neighborhoodSectionsModule A I M V) :
    neighborhoodSectionRestrict A I M f (a • x) =
      a • neighborhoodSectionRestrict A I M f x := sorry

/-- Restriction between two neighborhoods, bundled as an `A`-linear map on sections. -/
@[expose] noncomputable def neighborhoodSectionsModuleMap
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (I : Ideal A) (M : (scheme A).Modules)
    {V W : (Scheme.CoherentCompletion.compactSupport
      ((idealSheafDataOfIdealOnSpec I).comap (puncturedOpen A).ι)).openNhdsᵒᵖ}
    (f : V ⟶ W) :
    neighborhoodSectionsModule A I M V ⟶ neighborhoodSectionsModule A I M W :=
  (ConcreteCategory.ofHom
    ({ toFun := neighborhoodSectionRestrict A I M f,
        map_add' := neighborhoodSectionsMap_add A I M f,
        map_smul' := neighborhoodSectionsMap_smul A I M f } :
      neighborhoodSectionsModule A I M V →ₗ[A] neighborhoodSectionsModule A I M W) :
    neighborhoodSectionsModule A I M V ⟶ neighborhoodSectionsModule A I M W)

/-- The underlying function of `neighborhoodSectionsModuleMap` is restriction of sections. -/
theorem neighborhoodSectionsModuleMap_apply
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (I : Ideal A) (M : (scheme A).Modules)
    {V W : (Scheme.CoherentCompletion.compactSupport
      ((idealSheafDataOfIdealOnSpec I).comap (puncturedOpen A).ι)).openNhdsᵒᵖ}
    (f : V ⟶ W)
    (x : neighborhoodSectionsModule A I M V) :
    neighborhoodSectionsModuleMap A I M f x =
      neighborhoodSectionRestrict A I M f x := sorry

/-- Identity restriction gives the identity `A`-linear map on neighborhood sections. -/
theorem neighborhoodSectionsModuleMap_id
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (I : Ideal A) (M : (scheme A).Modules)
    (V : (Scheme.CoherentCompletion.compactSupport
      ((idealSheafDataOfIdealOnSpec I).comap (puncturedOpen A).ι)).openNhdsᵒᵖ) :
    neighborhoodSectionsModuleMap A I M (𝟙 V) =
      𝟙 (neighborhoodSectionsModule A I M V) := sorry

/-- Composite restriction gives the composite `A`-linear map on neighborhood sections. -/
theorem neighborhoodSectionsModuleMap_comp
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (I : Ideal A) (M : (scheme A).Modules)
    {U V W : (Scheme.CoherentCompletion.compactSupport
      ((idealSheafDataOfIdealOnSpec I).comap (puncturedOpen A).ι)).openNhdsᵒᵖ}
    (f : U ⟶ V) (g : V ⟶ W) :
    neighborhoodSectionsModuleMap A I M (f ≫ g) =
      neighborhoodSectionsModuleMap A I M f ≫
        neighborhoodSectionsModuleMap A I M g := sorry

/-- The canonical `ModuleCat A`-valued diagram of sections over neighborhoods of the
pullback of `V(I)`, with scalars restricted along the structural maps from `A`. -/
@[expose] noncomputable def neighborhoodSectionsModuleDiagram
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (I : Ideal A) (M : (scheme A).Modules) :
    (Scheme.CoherentCompletion.compactSupport
      ((idealSheafDataOfIdealOnSpec I).comap (puncturedOpen A).ι)).openNhdsᵒᵖ ⥤
        ModuleCat.{u} A where
  obj V := neighborhoodSectionsModule A I M V
  map f := neighborhoodSectionsModuleMap A I M f
  map_id V := neighborhoodSectionsModuleMap_id A I M V
  map_comp f g := neighborhoodSectionsModuleMap_comp A I M f g

/-- At a neighborhood `V`, the module-valued diagram is the section module obtained by
restriction of scalars from its structural `A`-algebra. -/
theorem neighborhoodSectionsModuleDiagram_obj
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (I : Ideal A) (M : (scheme A).Modules)
    (V : (Scheme.CoherentCompletion.compactSupport
      ((idealSheafDataOfIdealOnSpec I).comap (puncturedOpen A).ι)).openNhdsᵒᵖ) :
    (neighborhoodSectionsModuleDiagram A I M).obj V =
      neighborhoodSectionsModule A I M V := sorry

/-- The neighborhood-to-quotient-cohomology map preserves addition. -/
theorem neighborhoodSectionToQuotientCohomologyLimit_add
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (I : Ideal A) (M : (scheme A).Modules)
    (V : (Scheme.CoherentCompletion.compactSupport
      ((idealSheafDataOfIdealOnSpec I).comap (puncturedOpen A).ι)).openNhdsᵒᵖ)
    (x y : (neighborhoodSectionsModuleDiagram A I M).obj V) :
    neighborhoodSectionToQuotientCohomologyLimit A I M V (x + y) =
      neighborhoodSectionToQuotientCohomologyLimit A I M V x +
        neighborhoodSectionToQuotientCohomologyLimit A I M V y := sorry

/-- The neighborhood-to-quotient-cohomology map preserves the `A`-scalar action. -/
theorem neighborhoodSectionToQuotientCohomologyLimit_smul
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (I : Ideal A) (M : (scheme A).Modules)
    (V : (Scheme.CoherentCompletion.compactSupport
      ((idealSheafDataOfIdealOnSpec I).comap (puncturedOpen A).ι)).openNhdsᵒᵖ)
    (a : A) (x : (neighborhoodSectionsModuleDiagram A I M).obj V) :
    neighborhoodSectionToQuotientCohomologyLimit A I M V (a • x) =
      a • neighborhoodSectionToQuotientCohomologyLimit A I M V x := sorry

/-- The canonical `A`-linear map from sections on one neighborhood to the degree-zero
quotient-cohomology limit. -/
@[expose] noncomputable def neighborhoodSectionToQuotientCohomologyLimitLinear
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (I : Ideal A) (M : (scheme A).Modules)
    (V : (Scheme.CoherentCompletion.compactSupport
      ((idealSheafDataOfIdealOnSpec I).comap (puncturedOpen A).ι)).openNhdsᵒᵖ) :
    (neighborhoodSectionsModuleDiagram A I M).obj V ⟶
      limit (quotientCohomologySystem (puncturedOpen A).ι I M 0) :=
  (ConcreteCategory.ofHom
    ({ toFun := neighborhoodSectionToQuotientCohomologyLimit A I M V,
        map_add' := neighborhoodSectionToQuotientCohomologyLimit_add A I M V,
        map_smul' := neighborhoodSectionToQuotientCohomologyLimit_smul A I M V } :
      ((neighborhoodSectionsModuleDiagram A I M).obj V : Type u) →ₗ[A]
        (limit (quotientCohomologySystem (puncturedOpen A).ι I M 0) :
          ModuleCat.{u} A)) :
    (neighborhoodSectionsModuleDiagram A I M).obj V ⟶
      limit (quotientCohomologySystem (puncturedOpen A).ι I M 0))

/-- The underlying function of the linear stage map is the canonical map on sections. -/
theorem neighborhoodSectionToQuotientCohomologyLimitLinear_apply
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (I : Ideal A) (M : (scheme A).Modules)
    (V : (Scheme.CoherentCompletion.compactSupport
      ((idealSheafDataOfIdealOnSpec I).comap (puncturedOpen A).ι)).openNhdsᵒᵖ)
    (x : (neighborhoodSectionsModuleDiagram A I M).obj V) :
    neighborhoodSectionToQuotientCohomologyLimitLinear A I M V x =
      neighborhoodSectionToQuotientCohomologyLimit A I M V x := sorry

/-- The linear stage maps commute with restriction between neighborhoods. -/
theorem neighborhoodSectionToQuotientCohomologyLimitLinear_naturality
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (I : Ideal A) (M : (scheme A).Modules)
    {V W : (Scheme.CoherentCompletion.compactSupport
      ((idealSheafDataOfIdealOnSpec I).comap (puncturedOpen A).ι)).openNhdsᵒᵖ}
    (f : V ⟶ W) :
    (neighborhoodSectionsModuleDiagram A I M).map f ≫
        neighborhoodSectionToQuotientCohomologyLimitLinear A I M W =
      neighborhoodSectionToQuotientCohomologyLimitLinear A I M V ≫
        ((Functor.const (Scheme.CoherentCompletion.compactSupport
          ((idealSheafDataOfIdealOnSpec I).comap
            (puncturedOpen A).ι)).openNhdsᵒᵖ).obj
              (limit (quotientCohomologySystem
                (puncturedOpen A).ι I M 0))).map f := sorry

/-- The canonical `A`-linear map from the colimit of sections over neighborhoods of the
pullback of `V(I)` to the degree-zero quotient-cohomology limit. -/
@[expose] noncomputable def neighborhoodQuotientCohomologyComparison
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (I : Ideal A) (M : (scheme A).Modules) :
    colimit (neighborhoodSectionsModuleDiagram A I M) ⟶
      limit (quotientCohomologySystem (puncturedOpen A).ι I M 0) :=
  let c : Cocone (neighborhoodSectionsModuleDiagram A I M) :=
    { pt := limit (quotientCohomologySystem (puncturedOpen A).ι I M 0)
      ι :=
        { app := neighborhoodSectionToQuotientCohomologyLimitLinear A I M
          naturality := fun _ _ f ↦
            neighborhoodSectionToQuotientCohomologyLimitLinear_naturality A I M f } }
  colimit.desc _ c

/-- The comparison factors every colimit inclusion through the corresponding linear
neighborhood stage map. -/
theorem neighborhoodQuotientCohomologyComparison_fac
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (I : Ideal A) (M : (scheme A).Modules)
    (V : (Scheme.CoherentCompletion.compactSupport
      ((idealSheafDataOfIdealOnSpec I).comap (puncturedOpen A).ι)).openNhdsᵒᵖ) :
    colimit.ι (neighborhoodSectionsModuleDiagram A I M) V ≫
        neighborhoodQuotientCohomologyComparison A I M =
      neighborhoodSectionToQuotientCohomologyLimitLinear A I M V := sorry

/-- Let `A` be a Noetherian local ring with a dualizing complex
and let `A` be `I`-adically complete. If every associated point `x` of a coherent
module on the punctured spectrum has closure dimension greater than
`Ideal.LocalCohomology.dimension I I.fg_of_isNoetherianRing + 1`, then the
canonical `A`-linear map from sections over neighborhoods of the pullback of `V(I)`
to the degree-zero quotient-cohomology limit is an isomorphism, and that same limit
is a finite `A`-module. -/
theorem neighborhoodComparison_isIso_finite
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (h_dualizing : DerivedCategory.HasCanonicalDualizingComplex A)
    (I : Ideal A) [IsAdicComplete I A]
    (F : RingedSpace.Coh (scheme A).toRingedSpace)
    (h_dimension : ∀ x : scheme A, x ∈ associatedPoints F.obj →
      ((Ideal.LocalCohomology.dimension I
          I.fg_of_isNoetherianRing + 1 : ℤ) : EInt) <
        WithBot.map (WithTop.map Int.ofNat)
          (ringKrullDim (A ⧸ x.1.asIdeal))) :
    IsIso (neighborhoodQuotientCohomologyComparison A I
        ((Scheme.Modules.fromRingedSpace (scheme A)).obj F.obj)) ∧
      Module.Finite A
        ((limit (quotientCohomologySystem (puncturedOpen A).ι I
          ((Scheme.Modules.fromRingedSpace (scheme A)).obj F.obj) 0)) :
            ModuleCat.{u} A) := sorry

end AlgebraicGeometry.PuncturedSpectrum
