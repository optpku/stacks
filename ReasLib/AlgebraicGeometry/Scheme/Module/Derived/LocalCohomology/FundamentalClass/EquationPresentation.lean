module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.LocalCohomology.FundamentalClass.Functors
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Basic
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.ExteriorPower.DegreeOne
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.ExteriorPower.Multiplication
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.TopSections
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.AlgebraSheaf.Pullback
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.BaseChange
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pullback
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpenSubspace.Derived
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpenSubspace.Restriction
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Pullback.InternalHom
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Sections.Pushforward
public import ReasLib.Algebra.Homology.CochainComplex.Nat.Derived.Exact
public import ReasLib.CategoryTheory.Adjunction.BaseChange
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.LeftDerived
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Homology
public import ReasLib.AlgebraicGeometry.Scheme.Module.Conormal.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Module.Conormal.ClosedImmersion
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cech.PrincipalOpen.LocalCohomology.ChangeOfGenerators

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory ComplexShape Opposite
  TopologicalSpace
open SheafOfModules.ClosedSubset
open SheafOfModules.RingedSite.ExteriorPower
open scoped MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom.LocalCohomology

variable {X Z : Scheme.{u}}

/-- An affine equation chart for a closed immersion: an affine carrier together with `c`
equations generating the restricted kernel ideal. -/
structure EquationPresentation.{v} {X Z : Scheme.{v}} (i : Z ⟶ X)
    [IsClosedImmersion i] (c : ℕ) where
  /-- The ambient open on which the presentation is defined. -/
  carrier : X.Opens
  /-- The ambient open of an equation chart is affine. -/
  isAffine : IsAffineOpen carrier
  /-- The `c` local equations defining the restricted closed immersion. -/
  generators : Fin c → Γ(carrier.toScheme, ⊤)
  /-- The equations generate the kernel ideal sheaf of the restricted closed immersion. -/
  equations :
    Scheme.IdealSheafData.ofIdealTop (Ideal.span (Set.range generators)) =
      i.ker.comap carrier.ι

namespace EquationPresentation

/-- An equation presentation records an affine carrier and equations generating the restricted
kernel ideal sheaf. -/
theorem spec {i : Z ⟶ X} [IsClosedImmersion i] {c : ℕ}
    (P : EquationPresentation i c) :
    IsAffineOpen P.carrier ∧
      Scheme.IdealSheafData.ofIdealTop (Ideal.span (Set.range P.generators)) =
        i.ker.comap P.carrier.ι := sorry

/-- The closed immersion obtained by restricting the ambient closed immersion to an equation
chart. -/
abbrev restrictedImmersion {i : Z ⟶ X} [IsClosedImmersion i] {c : ℕ}
    (P : EquationPresentation i c) : (i ⁻¹ᵁ P.carrier).toScheme ⟶ P.carrier.toScheme :=
  i ∣_ P.carrier

/-- Each displayed equation belongs to the kernel of the restricted closed immersion. -/
theorem generator_mem_kernel {i : Z ⟶ X} [IsClosedImmersion i] {c : ℕ}
    (P : EquationPresentation i c) (k : Fin c) :
    P.generators k ∈ RingHom.ker (P.restrictedImmersion.appTop.hom) := sorry

/-- Each displayed equation is a section of the ambient kernel ideal on the equation chart. -/
theorem generator_mem_ambientKernel {i : Z ⟶ X} [IsClosedImmersion i] {c : ℕ}
    (P : EquationPresentation i c) (k : Fin c) :
    X.presheaf.map
        (eqToHom (P.carrier.ι.image_top_eq_opensRange.trans
          (Scheme.Opens.opensRange_ι P.carrier)).symm).op
        ((P.carrier.ι.appIso ⊤).inv (P.generators k)) ∈ RingHom.ker
      ((RingedSpace.Hom.commRingSheafPushforwardMap i.toShHom).hom.app
        (op P.carrier)).hom := sorry

/-- A displayed equation regarded as a section of the intrinsic kernel-ideal sheaf. -/
noncomputable def generatorKernelSection {i : Z ⟶ X} [IsClosedImmersion i] {c : ℕ}
    (P : EquationPresentation i c) (k : Fin c) :
    (RingedSpace.Hom.kernelIdealSheaf P.restrictedImmersion.toShHom).val.obj (op ⊤) :=
  (SheafOfModules.RingedSite.KernelIdeal.sectionsIso
    (RingedSpace.Hom.commRingSheafPushforwardMap P.restrictedImmersion.toShHom)
      (op ⊤)).inv ⟨P.generators k, P.generator_mem_kernel k⟩

/-- The conormal class of a displayed equation, formed by the canonical quotient
`I ⟶ I / I²`. -/
noncomputable def generatorConormalClass {i : Z ⟶ X} [IsClosedImmersion i] {c : ℕ}
    (P : EquationPresentation i c) (k : Fin c) :
    (Scheme.Hom.conormalSheaf P.restrictedImmersion).val.obj (op ⊤) :=
  (Scheme.Hom.Conormal.pushforwardConormalComparison
    P.restrictedImmersion).val.app (op ⊤)
      ((Scheme.Hom.Conormal.idealToCotangent
        P.restrictedImmersion).val.app (op ⊤) (P.generatorKernelSection k))

/-- A displayed equation regarded as a section of the global conormal sheaf over the inverse
image of the equation chart. -/
noncomputable def generatorGlobalConormalSection {i : Z ⟶ X}
    [IsClosedImmersion i] {c : ℕ} (P : EquationPresentation i c) (k : Fin c) :
    (Scheme.Hom.conormalSheaf i).val.obj (op (i ⁻¹ᵁ P.carrier)) :=
  (Scheme.Hom.Conormal.pushforwardConormalComparison i).val.app (op P.carrier)
    ((Scheme.Hom.Conormal.idealToCotangent i).val.app (op P.carrier)
      ((SheafOfModules.RingedSite.KernelIdeal.sectionsIso
        (RingedSpace.Hom.commRingSheafPushforwardMap i.toShHom)
          (op P.carrier)).inv
            ⟨X.presheaf.map
                (eqToHom (P.carrier.ι.image_top_eq_opensRange.trans
                  (Scheme.Opens.opensRange_ι P.carrier)).symm).op
                ((P.carrier.ι.appIso ⊤).inv (P.generators k)),
              P.generator_mem_ambientKernel k⟩))

/-- The ordered exterior product of a finite family of top-open sections. -/
noncomputable def orderedWedge {Y : Scheme.{u}} (M : Y.Modules) :
    (n : ℕ) → (Fin n → M.val.obj (op ⊤)) →
      (sheaf Y.𝒪 M n).val.obj (op ⊤)
  | 0, _ =>
      ((one Y.𝒪 M).val.app (op ⊤)).hom (1 : Y.𝒪.obj.obj (op ⊤))
  | n + 1, x =>
      ((eqToHom (congrArg (sheaf Y.𝒪 M) (Nat.add_comm 1 n))).val.app (op ⊤)).hom
        (((mul Y.𝒪 M 1 n).val.app (op ⊤)).hom
          (SheafOfModules.RingedSite.tensorSection Y.𝒪 (op ⊤)
            ((degreeOne Y.𝒪 M).val.app (op ⊤) (x 0))
            (orderedWedge M n (fun k ↦ x k.succ))))

/-- The ordered exterior product of a finite family of sections over an arbitrary open. -/
noncomputable def orderedWedgeAt {Y : Scheme.{u}} (M : Y.Modules) (V : Y.Opens) :
    (n : ℕ) → (Fin n → M.val.obj (op V)) →
      (sheaf Y.𝒪 M n).val.obj (op V)
  | 0, _ =>
      ((one Y.𝒪 M).val.app (op V)).hom (1 : Y.𝒪.obj.obj (op V))
  | n + 1, x =>
      ((eqToHom (congrArg (sheaf Y.𝒪 M) (Nat.add_comm 1 n))).val.app (op V)).hom
        (((mul Y.𝒪 M 1 n).val.app (op V)).hom
          (SheafOfModules.RingedSite.tensorSection Y.𝒪 (op V)
            ((degreeOne Y.𝒪 M).val.app (op V) (x 0))
            (orderedWedgeAt M V n (fun k ↦ x k.succ))))

/-- The ordered equation wedge as a section of the global conormal determinant over the
inverse-image chart. -/
noncomputable def globalEquationWedge {i : Z ⟶ X} [IsClosedImmersion i] {c : ℕ}
    (P : EquationPresentation i c) :
    (sheaf Z.𝒪 (Scheme.Hom.conormalSheaf i) c).val.obj
      (op (i ⁻¹ᵁ P.carrier)) :=
  orderedWedgeAt (Scheme.Hom.conormalSheaf i) (i ⁻¹ᵁ P.carrier) c
    P.generatorGlobalConormalSection

/-- The restriction of the global conormal determinant to an equation chart. -/
noncomputable abbrev restrictedGlobalDeterminant {i : Z ⟶ X}
    [IsClosedImmersion i] {c : ℕ} (P : EquationPresentation i c) :
    (i ⁻¹ᵁ P.carrier).toScheme.Modules :=
  (Scheme.Modules.pullback (i ⁻¹ᵁ P.carrier).ι).obj
    (sheaf Z.𝒪 (Scheme.Hom.conormalSheaf i) c)

/-- The ordered top exterior class of the local defining equations in the conormal sheaf of
the restricted closed immersion. -/
noncomputable def equationWedge {i : Z ⟶ X} [IsClosedImmersion i] {c : ℕ}
    (P : EquationPresentation i c) :
    (P.restrictedGlobalDeterminant).val.obj (op ⊤) :=
  ((Scheme.Modules.restrictFunctorIsoPullback
    (i ⁻¹ᵁ P.carrier).ι).hom.app
      (sheaf Z.𝒪 (Scheme.Hom.conormalSheaf i) c)).val.app (op ⊤)
    ((Scheme.Modules.restrictAppIso (i ⁻¹ᵁ P.carrier).ι
      (sheaf Z.𝒪 (Scheme.Hom.conormalSheaf i) c) ⊤).inv
        ((sheaf Z.𝒪 (Scheme.Hom.conormalSheaf i) c).val.map
          (eqToHom ((i ⁻¹ᵁ P.carrier).ι.image_top_eq_opensRange.trans
            (Scheme.Opens.opensRange_ι (i ⁻¹ᵁ P.carrier)))).op P.globalEquationWedge))

/-- The coefficient module restricted to the open of an equation presentation. -/
abbrev coefficients {i : Z ⟶ X} [IsClosedImmersion i] {c : ℕ}
    (P : EquationPresentation i c) (ℱ : Scheme.QCoh X) : P.carrier.toScheme.Modules :=
  (Scheme.Modules.restrictFunctor P.carrier.ι).obj ((Scheme.QCoh.inclusion X).obj ℱ)

/-- Evaluation of an internal-Hom dual against a specified top-open section. -/
noncomputable def dualEvaluationAtSection {Y : Scheme.{u}} (M : Y.Modules)
    (s : M.val.obj (op ⊤)) :
    (ihom M).obj (SheafOfModules.unit Y.ringCatSheaf) ⟶
      SheafOfModules.unit Y.ringCatSheaf :=
  (((ρ_ ((ihom M).obj (SheafOfModules.unit Y.ringCatSheaf))).symm) ≪≫
      ((Iso.refl ((ihom M).obj (SheafOfModules.unit Y.ringCatSheaf)) ⊗ᵢ
        SheafOfModules.RingedSite.unitIsoTensorUnit
          (J := Opens.grothendieckTopology Y.toTopCat) (𝒪 := Y.𝒪)).symm)).hom ≫
    tensorHom (𝟙 ((ihom M).obj (SheafOfModules.unit Y.ringCatSheaf)))
      (RingedSpace.topSectionMorphism M s) ≫
    (β_ ((ihom M).obj (SheafOfModules.unit Y.ringCatSheaf)) M).hom ≫
    (ihom.ev M).app (SheafOfModules.unit Y.ringCatSheaf)

/-- The local source functor: form the dual determinant and tensor product on the restricted
closed subscheme, then push the result to the ambient equation chart. -/
noncomputable def localSourceFunctor {i : Z ⟶ X} [IsClosedImmersion i] {c : ℕ}
    (P : EquationPresentation i c) :
    Scheme.QCoh X ⥤ P.carrier.toScheme.Modules :=
    Scheme.QCoh.inclusion X ⋙ Scheme.Modules.restrictFunctor P.carrier.ι ⋙
    Scheme.Modules.pullback P.restrictedImmersion ⋙
    MonoidalCategory.tensorLeft
      ((ihom P.restrictedGlobalDeterminant).obj
          (SheafOfModules.unit
            (i ⁻¹ᵁ P.carrier).toScheme.ringCatSheaf)) ⋙
    Scheme.Modules.pushforward P.restrictedImmersion

/-- The local coefficient after pullback to the restricted closed subscheme and pushforward
to the ambient equation chart. -/
noncomputable def localCoefficientFunctor {i : Z ⟶ X} [IsClosedImmersion i] {c : ℕ}
    (P : EquationPresentation i c) :
    Scheme.QCoh X ⥤ P.carrier.toScheme.Modules :=
  Scheme.QCoh.inclusion X ⋙ Scheme.Modules.restrictFunctor P.carrier.ι ⋙
    Scheme.Modules.pullback P.restrictedImmersion ⋙
    Scheme.Modules.pushforward P.restrictedImmersion

/-- The local Čech supported-cohomology functor associated to an equation chart. -/
noncomputable def localSupportedCohomologyFunctor {i : Z ⟶ X} [IsClosedImmersion i] {c : ℕ}
    (P : EquationPresentation i c) :=
  Scheme.QCoh.inclusion X ⋙ Scheme.Modules.restrictFunctor P.carrier.ι ⋙
    ModuleCech.LocalCohomology.cohomologyFunctor P.generators

/-- Sections of the global supported-cohomology sheaf over an equation chart. -/
noncomputable def supportedCohomologySectionsFunctor {i : Z ⟶ X}
    [IsClosedImmersion i] {c : ℕ} (P : EquationPresentation i c) :
    Scheme.QCoh X ⥤ AddCommGrpCat.{u} :=
  functor i c ⋙
    SheafOfModules.evaluation.{u} X.toRingedSpace.ringCatSheaf (op P.carrier) ⋙
    forget₂ (ModuleCat Γ(X, P.carrier)) AddCommGrpCat.{u}

/-- Top-open sections of the local Čech supported-cohomology model. -/
noncomputable def localSupportedCohomologySectionsFunctor {i : Z ⟶ X}
    [IsClosedImmersion i] {c : ℕ} (P : EquationPresentation i c) :
    Scheme.QCoh X ⥤ AddCommGrpCat.{u} :=
  localSupportedCohomologyFunctor P ⋙
    SheafOfModules.evaluation.{u}
      (SheafOfModules.ClosedSubset.ringSheaf
        P.carrier.toScheme.toRingedSpace.ringCatSheaf
        (ModuleCech.ofSectionsZeroLocus P.generators)) (op ⊤) ⋙
    forget₂ _ AddCommGrpCat.{u}

/-- The cartesian restriction square underlying an equation chart, viewed as a square of
ringed spaces. -/
theorem restrictionSquare {i : Z ⟶ X} [IsClosedImmersion i] {c : ℕ}
    (P : EquationPresentation i c) :
    CommSq (i ⁻¹ᵁ P.carrier).ι.toShHom P.restrictedImmersion.toShHom
      i.toShHom P.carrier.ι.toShHom :=
  (isPullback_morphismRestrict i P.carrier).flip.toCommSq.map
    (Scheme.forgetToLocallyRingedSpace ⋙
      LocallyRingedSpace.forgetToSheafedSpace)

/-- The canonical open base-change map for the pushed-forward global source tensor. -/
noncomputable def sourcePushforwardBaseChange {i : Z ⟶ X} [IsClosedImmersion i] {c : ℕ}
    (P : EquationPresentation i c) (ℱ : Scheme.QCoh X) :
    let M :=
      ((ihom (sheaf Z.𝒪 (Scheme.Hom.conormalSheaf i) c)).obj
        (SheafOfModules.unit Z.ringCatSheaf)) ⊗
        (Scheme.Modules.pullback i).obj ((Scheme.QCoh.inclusion X).obj ℱ)
    (RingedSpace.Hom.pullback P.carrier.ι.toShHom).obj
        ((RingedSpace.Hom.pushforward i.toShHom).obj M) ⟶
      (RingedSpace.Hom.pushforward P.restrictedImmersion.toShHom).obj
        ((RingedSpace.Hom.pullback (i ⁻¹ᵁ P.carrier).ι.toShHom).obj M) :=
  (RingedSpace.Hom.BaseChange.map (restrictionSquare P)).app _

/-- Pulling back the degree-`c` exterior power of the global conormal sheaf and then applying
the conormal base-change map gives the local degree-`c` exterior power. -/
noncomputable def exteriorPowerBaseChange {i : Z ⟶ X} [IsClosedImmersion i] {c : ℕ}
    (P : EquationPresentation i c) :
    (RingedSpace.Hom.pullback (i ⁻¹ᵁ P.carrier).ι.toShHom).obj
        (sheaf Z.𝒪 (Scheme.Hom.conormalSheaf i) c) ⟶
      sheaf (i ⁻¹ᵁ P.carrier).toScheme.𝒪
        (Scheme.Hom.conormalSheaf P.restrictedImmersion) c :=
  (Scheme.Modules.pullback (i ⁻¹ᵁ P.carrier).ι).map
      (SheafOfModules.RingedSite.ExteriorAlgebra.powerι
        Z.𝒪 (Scheme.Hom.conormalSheaf i) c) ≫
    RingedSpace.ExteriorAlg.Pullback.comparison
      (i ⁻¹ᵁ P.carrier).ι.toShHom (Scheme.Hom.conormalSheaf i) ≫
    (SheafOfModules.RingedSite.ExteriorAlgebra.decompositionAppIso
      (i ⁻¹ᵁ P.carrier).toScheme.𝒪
      ((Scheme.Modules.pullback (i ⁻¹ᵁ P.carrier).ι).obj
        (Scheme.Hom.conormalSheaf i))).hom ≫
    Limits.Sigma.π
      (SheafOfModules.RingedSite.ExteriorPower.gradedObject
        (i ⁻¹ᵁ P.carrier).toScheme.𝒪
        ((Scheme.Modules.pullback (i ⁻¹ᵁ P.carrier).ι).obj
          (Scheme.Hom.conormalSheaf i))) c ≫
    SheafOfModules.RingedSite.ExteriorPower.map
      (i ⁻¹ᵁ P.carrier).toScheme.𝒪
      (Scheme.Hom.Conormal.map
        (isPullback_morphismRestrict i P.carrier).flip.toCommSq) c

/-- The canonical comparison from the pulled-back global determinant dual to the dual of the
restricted global determinant. -/
noncomputable def dualBaseChange {i : Z ⟶ X} [IsClosedImmersion i] {c : ℕ}
    (P : EquationPresentation i c) :
    (RingedSpace.Hom.pullback (i ⁻¹ᵁ P.carrier).ι.toShHom).obj
        ((ihom (sheaf Z.𝒪 (Scheme.Hom.conormalSheaf i) c)).obj
          (SheafOfModules.unit Z.ringCatSheaf)) ⟶
      (ihom P.restrictedGlobalDeterminant).obj
          (SheafOfModules.unit
            (i ⁻¹ᵁ P.carrier).toScheme.ringCatSheaf) :=
  RingedSpace.Hom.PullbackInternalHom.comparison
      (i ⁻¹ᵁ P.carrier).ι.toShHom
      (sheaf Z.𝒪 (Scheme.Hom.conormalSheaf i) c)
      (SheafOfModules.unit Z.ringCatSheaf) ≫
    (ihom ((RingedSpace.Hom.pullback
      (i ⁻¹ᵁ P.carrier).ι.toShHom).obj
      (sheaf Z.𝒪 (Scheme.Hom.conormalSheaf i) c))).map
        (SheafOfModules.pullbackObjUnitToUnit
          (RingedSpace.Hom.toRingCatSheafHom
            (i ⁻¹ᵁ P.carrier).ι.toShHom))

/-- The canonical pullback-composition comparison for the coefficient module on an equation
chart. -/
noncomputable def coefficientBaseChange {i : Z ⟶ X} [IsClosedImmersion i] {c : ℕ}
    (P : EquationPresentation i c) (ℱ : Scheme.QCoh X) :
    (Scheme.Modules.pullback (i ⁻¹ᵁ P.carrier).ι).obj
        ((Scheme.Modules.pullback i).obj ((Scheme.QCoh.inclusion X).obj ℱ)) ⟶
      (Scheme.Modules.pullback P.restrictedImmersion).obj (P.coefficients ℱ) :=
  (RingedSpace.Hom.BaseChange.pullbackIso (restrictionSquare P)).inv.app
      ((Scheme.QCoh.inclusion X).obj ℱ) ≫
    (Scheme.Modules.pullback P.restrictedImmersion).map
      ((Scheme.Modules.restrictFunctorIsoPullback P.carrier.ι).inv.app
        ((Scheme.QCoh.inclusion X).obj ℱ))

/-- The canonical restriction/base-change comparison on the tensor forming the source of the
fundamental-class map. -/
noncomputable def sourceTensorBaseChange {i : Z ⟶ X} [IsClosedImmersion i] {c : ℕ}
    (P : EquationPresentation i c) (ℱ : Scheme.QCoh X) :
    (RingedSpace.Hom.pullback (i ⁻¹ᵁ P.carrier).ι.toShHom).obj
        (((ihom (sheaf Z.𝒪 (Scheme.Hom.conormalSheaf i) c)).obj
          (SheafOfModules.unit Z.ringCatSheaf)) ⊗
          (Scheme.Modules.pullback i).obj ((Scheme.QCoh.inclusion X).obj ℱ)) ⟶
      (MonoidalCategory.tensorLeft
        ((ihom P.restrictedGlobalDeterminant).obj
            (SheafOfModules.unit
              (i ⁻¹ᵁ P.carrier).toScheme.ringCatSheaf))).obj
        ((Scheme.Modules.pullback P.restrictedImmersion).obj
          ((Scheme.Modules.restrictFunctor P.carrier.ι).obj
            ((Scheme.QCoh.inclusion X).obj ℱ))) :=
  (RingedSpace.Hom.pullbackTensorIso (i ⁻¹ᵁ P.carrier).ι.toShHom
      ((ihom (sheaf Z.𝒪 (Scheme.Hom.conormalSheaf i) c)).obj
        (SheafOfModules.unit Z.ringCatSheaf))
      ((Scheme.Modules.pullback i).obj ((Scheme.QCoh.inclusion X).obj ℱ))).hom ≫
    @tensorHom (RingedSpace.Modules (i ⁻¹ᵁ P.carrier).toScheme.toRingedSpace) _
      (RingedSpace.modulesMonoidalCategory
        (i ⁻¹ᵁ P.carrier).toScheme.toRingedSpace).toMonoidalCategoryStruct
      _ _ _ _ (dualBaseChange P) (coefficientBaseChange P ℱ)

/-- The global source restricted to an equation chart maps canonically to the source model
built from the restricted conormal sheaf and restricted coefficient. -/
noncomputable def sourceBaseChange {i : Z ⟶ X} [IsClosedImmersion i] {c : ℕ}
    (P : EquationPresentation i c) (ℱ : Scheme.QCoh X) :
    let M :=
      ((ihom (sheaf Z.𝒪 (Scheme.Hom.conormalSheaf i) c)).obj
        (SheafOfModules.unit Z.ringCatSheaf)) ⊗
        (Scheme.Modules.pullback i).obj ((Scheme.QCoh.inclusion X).obj ℱ)
    (RingedSpace.Hom.pullback P.carrier.ι.toShHom).obj
        ((RingedSpace.Hom.pushforward i.toShHom).obj M) ⟶
      (P.localSourceFunctor).obj ℱ :=
  sourcePushforwardBaseChange P ℱ ≫
    (Scheme.Modules.pushforward P.restrictedImmersion).map
      (sourceTensorBaseChange P ℱ)

/-- Derived restriction of a globally supported object to an equation chart, followed by the
canonical local supported-section coreflector. -/
noncomputable def supportedDerivedPullback {i : Z ⟶ X} [IsClosedImmersion i] {c : ℕ}
    (P : EquationPresentation i c) :
    ModuleDerived X.toRingedSpace.ringCatSheaf i.ker.support ⥤
      ModuleDerived P.carrier.toScheme.toRingedSpace.ringCatSheaf
        (ModuleCech.ofSectionsZeroLocus P.generators) :=
  (Derived.pushforward X.toRingedSpace.ringCatSheaf i.ker.support ⋙
      RingedSpace.OpenSubspace.Restriction.derivedPullback X.toRingedSpace P.carrier) ⋙
    Derived.sectionsWithSupport P.carrier.toScheme.toRingedSpace.ringCatSheaf
      (ModuleCech.ofSectionsZeroLocus P.generators)

/-- The canonical counit comparison from locally supported restriction back to unrestricted
open restriction. -/
noncomputable def supportedPushforwardComparison {i : Z ⟶ X}
    [IsClosedImmersion i] {c : ℕ} (P : EquationPresentation i c) :
    supportedDerivedPullback P ⋙
        Derived.pushforward P.carrier.toScheme.toRingedSpace.ringCatSheaf
          (ModuleCech.ofSectionsZeroLocus P.generators) ⟶
      Derived.pushforward X.toRingedSpace.ringCatSheaf i.ker.support ⋙
        RingedSpace.OpenSubspace.Restriction.derivedPullback X.toRingedSpace P.carrier :=
  (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft
      (Derived.pushforward X.toRingedSpace.ringCatSheaf i.ker.support ⋙
        RingedSpace.OpenSubspace.Restriction.derivedPullback X.toRingedSpace P.carrier)
      (Derived.adjunction P.carrier.toScheme.toRingedSpace.ringCatSheaf
        (ModuleCech.ofSectionsZeroLocus P.generators)).counit

/-- Restriction of a globally supported derived object to an equation chart is still supported
on the common zero locus of the displayed equations. -/
theorem supportedPushforwardComparison_isIso {i : Z ⟶ X}
    [IsClosedImmersion i] {c : ℕ} (P : EquationPresentation i c) :
    IsIso (supportedPushforwardComparison P) := sorry

/-- The canonical derived base-change map for supported sections on an equation chart. -/
noncomputable def supportedDerivedRestriction {i : Z ⟶ X}
    [IsClosedImmersion i] {c : ℕ} (P : EquationPresentation i c) :
    Derived.sectionsWithSupport X.toRingedSpace.ringCatSheaf i.ker.support ⋙
        supportedDerivedPullback P ⟶
      RingedSpace.OpenSubspace.Restriction.derivedPullback X.toRingedSpace P.carrier ⋙
        Derived.sectionsWithSupport P.carrier.toScheme.toRingedSpace.ringCatSheaf
          (ModuleCech.ofSectionsZeroLocus P.generators) :=
  CategoryTheory.DerivedBaseChange.map
    (Derived.adjunction X.toRingedSpace.ringCatSheaf i.ker.support)
    (Derived.adjunction P.carrier.toScheme.toRingedSpace.ringCatSheaf
      (ModuleCech.ofSectionsZeroLocus P.generators))
    (@asIso _ _ _ _ (supportedPushforwardComparison P)
      (supportedPushforwardComparison_isIso P))

/-- Derived open restriction of a coefficient sheaf in degree zero, compared with ordinary
restriction of that coefficient. -/
noncomputable def coefficientDerivedRestriction {i : Z ⟶ X}
    [IsClosedImmersion i] {c : ℕ} (P : EquationPresentation i c)
    (ℱ : Scheme.QCoh X) :
    (RingedSpace.OpenSubspace.Restriction.derivedPullback X.toRingedSpace P.carrier).obj
        ((ModuleCech.moduleToDerived X).obj ((Scheme.QCoh.inclusion X).obj ℱ)) ⟶
      (ModuleCech.moduleToDerived P.carrier.toScheme).obj (P.coefficients ℱ) :=
  let M := (Scheme.QCoh.inclusion X).obj ℱ
  let K := ((Scheme.Modules.toRingedSpace X).mapHomologicalComplex (up ℕ)).obj
    ((CochainComplex.single₀ X.Modules).obj M)
  (RingedSpace.OpenSubspace.Restriction.derivedPullback X.toRingedSpace P.carrier).map
      ((DerivedCategory.quotientCompQhIso X.toRingedSpace.Modules).inv.app
        (K.extend embeddingUpNat)) ≫
    ((RingedSpace.modulePullbackToDerived
      P.carrier.ι.toShHom).totalLeftDerivedCounit
        DerivedCategory.Qh (RingedSpace.ModuleQis X.toRingedSpace)).app
          ((HomotopyCategory.quotient X.toRingedSpace.Modules (up ℤ)).obj
            (K.extend embeddingUpNat)) ≫
    DerivedCategory.Q.map
      (ComplexShape.Embedding.mapAppIso embeddingUpNat
        (RingedSpace.Hom.pullback P.carrier.ι.toShHom) K).hom ≫
    (ModuleCech.toRingedSpaceDerived P.carrier.toScheme).map
      ((HomologicalComplex.singleMapHomologicalComplex
        (Scheme.Modules.pullback P.carrier.ι) (up ℕ) 0).hom.app M) ≫
    (ModuleCech.moduleToDerived P.carrier.toScheme).map
      ((Scheme.Modules.restrictFunctorIsoPullback P.carrier.ι).inv.app M)

/-- Derived restriction of the pushed-forward supported object to an equation chart. -/
noncomputable def supportedDerivedRestrictionApp {i : Z ⟶ X}
    [IsClosedImmersion i] {c : ℕ} (P : EquationPresentation i c)
    (ℱ : Scheme.QCoh X) :
    let K := (ModuleCech.moduleToDerived X).obj ((Scheme.QCoh.inclusion X).obj ℱ)
    let A := (Derived.sectionsWithSupport X.toRingedSpace.ringCatSheaf
      i.ker.support).obj K
    let B := (Derived.sectionsWithSupport
      P.carrier.toScheme.toRingedSpace.ringCatSheaf
        (ModuleCech.ofSectionsZeroLocus P.generators)).obj
          ((ModuleCech.moduleToDerived P.carrier.toScheme).obj (P.coefficients ℱ))
    (RingedSpace.OpenSubspace.Restriction.derivedPullback X.toRingedSpace P.carrier).obj
        ((Derived.pushforward X.toRingedSpace.ringCatSheaf i.ker.support).obj A) ⟶
      (Derived.pushforward P.carrier.toScheme.toRingedSpace.ringCatSheaf
        (ModuleCech.ofSectionsZeroLocus P.generators)).obj B :=
  let K := (ModuleCech.moduleToDerived X).obj ((Scheme.QCoh.inclusion X).obj ℱ)
  let A := (Derived.sectionsWithSupport X.toRingedSpace.ringCatSheaf
    i.ker.support).obj K
  (@asIso _ _ _ _ (supportedPushforwardComparison P)
    (supportedPushforwardComparison_isIso P)).inv.app A ≫
    (Derived.pushforward P.carrier.toScheme.toRingedSpace.ringCatSheaf
      (ModuleCech.ofSectionsZeroLocus P.generators)).map
        ((supportedDerivedRestriction P).app K ≫
          (Derived.sectionsWithSupport
            P.carrier.toScheme.toRingedSpace.ringCatSheaf
              (ModuleCech.ofSectionsZeroLocus P.generators)).map
                (coefficientDerivedRestriction P ℱ))

/-- The canonical open-restriction/base-change morphism on the degree-`c` supported-cohomology
module. -/
noncomputable def supportedModuleRestriction {i : Z ⟶ X}
    [IsClosedImmersion i] {c : ℕ} (P : EquationPresentation i c)
    (ℱ : Scheme.QCoh X) :
    (RingedSpace.Hom.pullback P.carrier.ι.toShHom).obj ((functor i c).obj ℱ) ⟶
      (SheafOfModules.ClosedSubset.pushforward
        P.carrier.toScheme.toRingedSpace.ringCatSheaf
          (ModuleCech.ofSectionsZeroLocus P.generators)).obj
            ((ModuleCech.LocalCohomology.cohomologyFunctor P.generators).obj
              (P.coefficients ℱ)) :=
  let K := (ModuleCech.moduleToDerived X).obj ((Scheme.QCoh.inclusion X).obj ℱ)
  let A := (Derived.sectionsWithSupport X.toRingedSpace.ringCatSheaf
    i.ker.support).obj K
  let B := (Derived.sectionsWithSupport
    P.carrier.toScheme.toRingedSpace.ringCatSheaf
      (ModuleCech.ofSectionsZeroLocus P.generators)).obj
        ((ModuleCech.moduleToDerived P.carrier.toScheme).obj (P.coefficients ℱ))
  let E := (Derived.pushforward X.toRingedSpace.ringCatSheaf i.ker.support).obj A
  let H := DerivedCategory.homologyFunctor
    P.carrier.toScheme.toRingedSpace.Modules (c : ℤ)
  let pushforwardExact := ExactFunctor.of
    (SheafOfModules.ClosedSubset.pushforward
      P.carrier.toScheme.toRingedSpace.ringCatSheaf
        (ModuleCech.ofSectionsZeroLocus P.generators))
  (RingedSpace.Hom.pullback P.carrier.ι.toShHom).map
      (((ExactFunctor.of (SheafOfModules.ClosedSubset.pushforward
        X.toRingedSpace.ringCatSheaf i.ker.support)).homologyFunctorIso
          (c : ℤ)).inv.app A) ≫
    (RingedSpace.OpenSubspace.Restriction.derivedPullbackHomologyIso
      X.toRingedSpace P.carrier E (c : ℤ)).hom ≫
    H.map (supportedDerivedRestrictionApp P ℱ) ≫
    (pushforwardExact.homologyFunctorIso (c : ℤ)).hom.app B

/-- Evaluation of the top exterior dual on the ordered equation class, before restriction to
the common zero locus. -/
noncomputable def equationEvaluation {i : Z ⟶ X} [IsClosedImmersion i] {c : ℕ}
    (P : EquationPresentation i c) (ℱ : Scheme.QCoh X) :
    (P.localSourceFunctor).obj ℱ ⟶ (P.localCoefficientFunctor).obj ℱ :=
  (Scheme.Modules.pushforward P.restrictedImmersion).map
    (tensorHom
        (dualEvaluationAtSection
          P.restrictedGlobalDeterminant
          P.equationWedge)
        (𝟙 ((Scheme.Modules.pullback P.restrictedImmersion).obj (P.coefficients ℱ))) ≫
      (SheafOfModules.RingedSite.unitIsoTensorUnit
        (J := Opens.grothendieckTopology (i ⁻¹ᵁ P.carrier).toScheme.toTopCat)
        (𝒪 := (i ⁻¹ᵁ P.carrier).toScheme.𝒪)).hom ▷
          (Scheme.Modules.pullback P.restrictedImmersion).obj (P.coefficients ℱ) ≫
      (λ_ ((Scheme.Modules.pullback P.restrictedImmersion).obj (P.coefficients ℱ))).hom)

/-- The forward canonical restriction/base-change comparison for the source on an equation
chart. -/
noncomputable def sourceRestriction {i : Z ⟶ X} [IsClosedImmersion i] {c : ℕ}
    (P : EquationPresentation i c) (ℱ : Scheme.QCoh X) :
    ((sourceFunctor i c).obj ℱ).val.presheaf.obj (op P.carrier) ⟶
      ((P.localSourceFunctor).obj ℱ).val.presheaf.obj (op ⊤) :=
  let M :=
    ((ihom (sheaf Z.𝒪 (Scheme.Hom.conormalSheaf i) c)).obj
      (SheafOfModules.unit Z.ringCatSheaf)) ⊗
      (Scheme.Modules.pullback i).obj ((Scheme.QCoh.inclusion X).obj ℱ)
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
      ((sourceBaseChange P ℱ).val.app (op ⊤)).hom.toAddMonoidHom

/-- Multiplication by the restricted closed-immersion ideal on the local coefficient. -/
noncomputable def coefficientIdealTensorMap {i : Z ⟶ X} [IsClosedImmersion i]
    {c : ℕ} (P : EquationPresentation i c) (ℱ : Scheme.QCoh X) :
    (RingedSpace.Hom.idealSheaf P.restrictedImmersion.toShHom) ⊗
        (P.coefficients ℱ) ⟶ P.coefficients ℱ :=
    tensorHom (RingedSpace.Hom.idealSheafι P.restrictedImmersion.toShHom)
      (𝟙 (P.coefficients ℱ)) ≫
    tensorHom
      (SheafOfModules.RingedSite.unitIsoTensorUnit
        (J := Opens.grothendieckTopology P.carrier.toScheme.toTopCat)
        (𝒪 := P.carrier.toScheme.𝒪)).hom
      (𝟙 (P.coefficients ℱ)) ≫
    (λ_ (P.coefficients ℱ)).hom

/-- Restriction of the local coefficient to the restricted closed subscheme. -/
noncomputable def coefficientRestrictionMap {i : Z ⟶ X} [IsClosedImmersion i]
    {c : ℕ} (P : EquationPresentation i c) (ℱ : Scheme.QCoh X) :
    P.coefficients ℱ ⟶ (P.localCoefficientFunctor).obj ℱ :=
  (SheafOfModules.pullbackPushforwardAdjunction
    (RingedSpace.Hom.toRingCatSheafHom P.restrictedImmersion.toShHom)).unit.app
      (P.coefficients ℱ)

/-- Multiplication by the restricted immersion ideal vanishes after restriction. -/
theorem coefficientIdealTensorMap_comp_restrictionMap {i : Z ⟶ X}
    [IsClosedImmersion i] {c : ℕ} (P : EquationPresentation i c)
    (ℱ : Scheme.QCoh X) :
    coefficientIdealTensorMap P ℱ ≫ coefficientRestrictionMap P ℱ = 0 := sorry

/-- The canonical ideal-tensor-to-restriction short complex on an equation chart. -/
noncomputable def coefficientRestrictionSequence {i : Z ⟶ X}
    [IsClosedImmersion i] {c : ℕ} (P : EquationPresentation i c)
    (ℱ : Scheme.QCoh X) : ShortComplex P.carrier.toScheme.Modules :=
  ShortComplex.mk (coefficientIdealTensorMap P ℱ) (coefficientRestrictionMap P ℱ)
    (coefficientIdealTensorMap_comp_restrictionMap P ℱ)

/-- The ideal-tensor sequence for the restricted closed immersion is exact at the coefficient
and its restriction. -/
theorem coefficientRestrictionSequence_exact {i : Z ⟶ X} [IsClosedImmersion i]
    {c : ℕ} (P : EquationPresentation i c) (ℱ : Scheme.QCoh X) :
    (coefficientRestrictionSequence P ℱ).Exact := sorry

/-- Restriction of a module to the closed subscheme and pushforward is an epimorphic quotient. -/
theorem coefficientRestrictionMap_epi {i : Z ⟶ X}
    [IsClosedImmersion i] {c : ℕ} (P : EquationPresentation i c)
    (ℱ : Scheme.QCoh X) :
    Epi (coefficientRestrictionSequence P ℱ).g := sorry

/-- The displayed equations act trivially after passage to their finite-family quotient. -/
theorem idealTensorMap_comp_quotientProjection {i : Z ⟶ X}
    [IsClosedImmersion i] {c : ℕ} (P : EquationPresentation i c)
    (ℱ : Scheme.QCoh X) :
    coefficientIdealTensorMap P ℱ ≫
      (ModuleCech.LocalCohomology.quotientProjection P.generators).app
        (P.coefficients ℱ) = 0 := sorry

/-- The pushed-forward pullback coefficient maps canonically to the quotient by the displayed
equations by the universal property of the closed-immersion restriction quotient. -/
noncomputable def coefficientQuotient {i : Z ⟶ X} [IsClosedImmersion i] {c : ℕ}
    (P : EquationPresentation i c) (ℱ : Scheme.QCoh X) :
    (Scheme.Modules.toRingedSpace P.carrier.toScheme).obj
        ((P.localCoefficientFunctor).obj ℱ) ⟶
      (ModuleCech.LocalCohomology.quotientFunctor P.generators).obj (P.coefficients ℱ) :=
  @ShortComplex.Exact.desc _ _ _ (coefficientRestrictionSequence P ℱ) _
    (coefficientRestrictionSequence_exact P ℱ) _
    ((ModuleCech.LocalCohomology.quotientProjection P.generators).app
      (P.coefficients ℱ))
    (idealTensorMap_comp_quotientProjection P ℱ) (coefficientRestrictionMap_epi P ℱ)

/-- The canonical restriction of the finite-family quotient to the common closed zero locus. -/
noncomputable def restrictQuotientToZeroLocus {i : Z ⟶ X} [IsClosedImmersion i] {c : ℕ}
    (P : EquationPresentation i c) (ℱ : Scheme.QCoh X) :
    ((ModuleCech.LocalCohomology.quotientFunctor P.generators).obj
        (P.coefficients ℱ)).val.presheaf.obj (op ⊤) ⟶
      ((ModuleCech.LocalCohomology.zeroLocusPullback P.generators).obj
        (P.coefficients ℱ)).val.presheaf.obj (op ⊤) :=
  (forget₂ _ _).map
    (((SheafOfModules.pullbackPushforwardAdjunction
      (SheafOfModules.ClosedSubset.structureMap
        P.carrier.toScheme.toRingedSpace.ringCatSheaf
        (ModuleCech.ofSectionsZeroLocus P.generators))).unit.app
          ((ModuleCech.LocalCohomology.quotientFunctor P.generators).obj
            (P.coefficients ℱ))).val.app (op ⊤))

/-- The canonical comparison from the coefficient on the restricted closed subscheme to the
coefficient on the common zero locus of the displayed equations. -/
noncomputable def coefficientComparison {i : Z ⟶ X} [IsClosedImmersion i] {c : ℕ}
    (P : EquationPresentation i c) (ℱ : Scheme.QCoh X) :
    ((P.localCoefficientFunctor).obj ℱ).val.presheaf.obj (op ⊤) ⟶
      ((ModuleCech.LocalCohomology.zeroLocusPullback P.generators).obj
        (P.coefficients ℱ)).val.presheaf.obj (op ⊤) :=
  (forget₂ _ _).map ((coefficientQuotient P ℱ).val.app (op ⊤)) ≫
    restrictQuotientToZeroLocus P ℱ

/-- The canonical coefficient comparison is natural in the quasicoherent coefficient. -/
theorem coefficientComparison_naturality {i : Z ⟶ X} [IsClosedImmersion i] {c : ℕ}
    (P : EquationPresentation i c) {ℱ 𝒢 : Scheme.QCoh X} (φ : ℱ ⟶ 𝒢) :
    (forget₂ _ _).map
        (((localCoefficientFunctor P).map φ).val.app (op ⊤)) ≫
        coefficientComparison P 𝒢 =
      coefficientComparison P ℱ ≫
        (forget₂ _ _).map
          (((ModuleCech.LocalCohomology.zeroLocusPullback P.generators).map
            ((Scheme.Modules.restrictFunctor P.carrier.ι).map
              ((Scheme.QCoh.inclusion X).map φ))).val.app (op ⊤)) := sorry

/-- The component of canonical open restriction and derived base change for supported
cohomology. -/
noncomputable def supportedRestrictionApp {i : Z ⟶ X} [IsClosedImmersion i] {c : ℕ}
    (P : EquationPresentation i c) (ℱ : Scheme.QCoh X) :
    ((functor i c).obj ℱ).val.presheaf.obj (op P.carrier) ⟶
      ((ModuleCech.LocalCohomology.cohomologyFunctor P.generators).obj
        (P.coefficients ℱ)).val.presheaf.obj (op ⊤) :=
  let N := (functor i c).obj ℱ
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
      ((supportedModuleRestriction P ℱ).val.app (op ⊤)).hom.toAddMonoidHom

/-- Canonical open restriction and derived base change for supported cohomology, natural in the
quasicoherent coefficient. -/
noncomputable def supportedRestriction {i : Z ⟶ X} [IsClosedImmersion i] {c : ℕ}
    (P : EquationPresentation i c) :
    supportedCohomologySectionsFunctor P ⟶
      localSupportedCohomologySectionsFunctor P where
  app ℱ := supportedRestrictionApp P ℱ
  naturality _ _ _ := sorry

/-- Canonical restriction to an equation chart is an isomorphism on supported cohomology. -/
theorem supportedRestriction_app_isIso {i : Z ⟶ X}
    [IsClosedImmersion i] {c : ℕ} (P : EquationPresentation i c)
    (ℱ : Scheme.QCoh X) : IsIso ((supportedRestriction P).app ℱ) := sorry

/-- The explicit chart source map: evaluate the top-conormal dual on the ordered wedge of the
equation classes and then descend the coefficient module to the common zero locus. -/
noncomputable def sourceComparison {i : Z ⟶ X} [IsClosedImmersion i] {c : ℕ}
    (P : EquationPresentation i c) (ℱ : Scheme.QCoh X) :
    ((sourceFunctor i c).obj ℱ).val.presheaf.obj (op P.carrier) ⟶
      ((ModuleCech.LocalCohomology.zeroLocusPullback P.generators).obj
        (P.coefficients ℱ)).val.presheaf.obj (op ⊤) :=
  sourceRestriction P ℱ ≫
    (forget₂ _ _).map ((P.equationEvaluation ℱ).val.app (op ⊤)) ≫
    coefficientComparison P ℱ

/-- The explicit chart target map is the inverse of canonical open-restriction base change for
cohomology with support. -/
noncomputable def targetComparison {i : Z ⟶ X} [IsClosedImmersion i] {c : ℕ}
    (P : EquationPresentation i c) (ℱ : Scheme.QCoh X) :
      ((ModuleCech.LocalCohomology.cohomologyFunctor P.generators).obj
        (P.coefficients ℱ)).val.presheaf.obj (op ⊤) ⟶
      ((functor i c).obj ℱ).val.presheaf.obj (op P.carrier) :=
  @inv _ _ _ _ ((supportedRestriction P).app ℱ)
    (supportedRestriction_app_isIso P ℱ)

/-- The equation-induced source comparison is natural in the quasicoherent coefficient module. -/
theorem sourceComparison_naturality {i : Z ⟶ X} [IsClosedImmersion i] {c : ℕ}
    (P : EquationPresentation i c)
    {ℱ 𝒢 : Scheme.QCoh X} (φ : ℱ ⟶ 𝒢) :
    (forget₂ _ _).map (((sourceFunctor i c).map φ).val.app (op P.carrier)) ≫
        sourceComparison P 𝒢 =
      sourceComparison P ℱ ≫
        (forget₂ _ _).map
          (((ModuleCech.LocalCohomology.zeroLocusPullback P.generators).map
            ((Scheme.Modules.restrictFunctor P.carrier.ι).map
              ((Scheme.QCoh.inclusion X).map φ))).val.app (op ⊤)) := sorry

/-- The supported-cohomology comparison on an equation chart is natural in the coefficient
module. -/
theorem targetComparison_naturality {i : Z ⟶ X} [IsClosedImmersion i] {c : ℕ}
    (P : EquationPresentation i c)
    {ℱ 𝒢 : Scheme.QCoh X} (φ : ℱ ⟶ 𝒢) :
    (forget₂ _ _).map
        (((ModuleCech.LocalCohomology.cohomologyFunctor P.generators).map
          ((Scheme.Modules.restrictFunctor P.carrier.ι).map
            ((Scheme.QCoh.inclusion X).map φ))).val.app (op ⊤)) ≫
        targetComparison P 𝒢 =
      targetComparison P ℱ ≫
        (forget₂ _ _).map (((functor i c).map φ).val.app (op P.carrier)) := sorry

/-- The local section map on an equation chart, obtained from the quotient-descended
generator class through the conormal evaluation and support-restriction comparisons. -/
noncomputable def localMap {i : Z ⟶ X} [IsClosedImmersion i] {c : ℕ}
  (P : EquationPresentation i c) (ℱ : Scheme.QCoh X) :
    ((sourceFunctor i c).obj ℱ).val.presheaf.obj (op P.carrier) ⟶
      ((functor i c).obj ℱ).val.presheaf.obj (op P.carrier) :=
  sourceComparison P ℱ ≫
    (forget₂ _ _).map
      (((ModuleCech.LocalCohomology.quotientClassMap P.generators).app
        (P.coefficients ℱ)).val.app (op ⊤)) ≫
    targetComparison P ℱ

/-- The local equation-chart map is independent of a change of ordered generators presenting
the same ambient open and kernel ideal. -/
theorem localMap_mulVec {i : Z ⟶ X} [IsClosedImmersion i] {c : ℕ}
    (P Q : EquationPresentation i c)
    (hcarrier : P.carrier = Q.carrier)
    (A : Matrix (Fin c) (Fin c) Γ(P.carrier.toScheme, ⊤))
    (hgenerators : P.generators = Matrix.mulVec A
      (fun j ↦ (X.homOfLE (le_of_eq hcarrier)).appTop.hom (Q.generators j)))
    (ℱ : Scheme.QCoh X) :
    HEq (localMap P ℱ) (localMap Q ℱ) := sorry

/-- A change-of-generators matrix exists after restricting one affine equation chart inside
another.  Compatibility of class maps is not accepted as transition data. -/
theorem exists_changeOfGenerators {i : Z ⟶ X} [IsClosedImmersion i] {c : ℕ}
    (P Q : EquationPresentation i c) (le : P.carrier ≤ Q.carrier) :
    ∃ A : Matrix (Fin c) (Fin c) Γ(P.carrier.toScheme, ⊤),
      P.generators = Matrix.mulVec A
        (fun j ↦ (X.homOfLE le).appTop.hom (Q.generators j)) := sorry

/-- The local equation-chart map is independent of the chosen ordered generators.  On an
affine carrier this follows by choosing a change matrix and applying
`ModuleCech.LocalCohomology.classMap_mulVec`. -/
theorem localMap_changeOfGenerators {i : Z ⟶ X} [IsClosedImmersion i] {c : ℕ}
    (P Q : EquationPresentation i c)
    (hcarrier : P.carrier = Q.carrier)
    (ℱ : Scheme.QCoh X) :
    HEq (localMap P ℱ) (localMap Q ℱ) := sorry

end EquationPresentation

end AlgebraicGeometry.Scheme.Hom.LocalCohomology

end
