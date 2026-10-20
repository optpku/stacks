module

public import ReasLib.AlgebraicGeometry.Scheme.DeRham.Gysin.ClosedImmersion
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.LocalCohomology.KoszulRegular
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Cohomology.Pullback
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.GlobalSections.Pushforward.Cohomology
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.ClosedImmersion.Pushforward
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Homotopy.Exact
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RegularImmersion
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.Differentials
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DeRham
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Cohomology.Map
public import ReasLib.CategoryTheory.Sites.Cohomology.Zero

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  Opposite RingedSpace Scheme.Hom SheafOfModules.RingedSite TopologicalSpace
open RingedSpace.ModuleDerived
open SheafOfModules.ClosedSubset SheafOfModules.ClosedSubset.SupportedDerived
open SheafOfModules.RingedSite.ExteriorAlgebra
  SheafOfModules.RingedSite.ExteriorPower
  Scheme.Hom.LocalCohomology
open scoped AlgebraicGeometry MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry
namespace Scheme.DeRham.Gysin

variable {Z X S : Scheme.{u}}

/-- The cohomology map realizing inverse image of ambient relative forms along
`i : Z ⟶ X`, represented on `X` by the pullback–pushforward unit. -/
noncomputable def inverseImage (i : Z ⟶ X) (f : X ⟶ S) (p q : ℕ) :
    RingedSpace.moduleCohomology
          ((Scheme.Modules.toRingedSpace X).obj (sheaf X.𝒪 Ω[f.toShHom] p)) q ⟶
      RingedSpace.moduleCohomology
        ((Scheme.Modules.toRingedSpace X).obj
          ((Scheme.Modules.pushforward i).obj
            ((Scheme.Modules.pullback i).obj (sheaf X.𝒪 Ω[f.toShHom] p)))) q :=
  RingedSpace.moduleCohomologyMap
    ((Scheme.Modules.toRingedSpace X).map
      ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app
        (sheaf X.𝒪 Ω[f.toShHom] p))) q

/-- The inverse-image cohomology map is induced by the canonical
pullback–pushforward unit. -/
theorem inverseImage_spec (i : Z ⟶ X) (f : X ⟶ S) (p q : ℕ) :
    inverseImage i f p q =
      RingedSpace.moduleCohomologyMap
        ((Scheme.Modules.toRingedSpace X).map
          ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app
            (sheaf X.𝒪 Ω[f.toShHom] p))) q := sorry

/-- The restriction map from ambient Hodge cohomology to the cohomology of
`Ω^p_{Z/S}`, represented by pushforward to `X`. -/
noncomputable def restriction (i : Z ⟶ X) (f : X ⟶ S) (p q : ℕ) :
    RingedSpace.moduleCohomology
          ((Scheme.Modules.toRingedSpace X).obj (sheaf X.𝒪 Ω[f.toShHom] p)) q ⟶
      RingedSpace.moduleCohomology
        ((Scheme.Modules.toRingedSpace X).obj
          ((Scheme.Modules.pushforward i).obj
            (sheaf Z.𝒪 Ω[(i ≫ f).toShHom] p))) q :=
  inverseImage i f p q ≫
    RingedSpace.moduleCohomologyMap
      ((Scheme.Modules.toRingedSpace X).map
        ((Scheme.Modules.pushforward i).map
          (pullbackFormToClosedForm i f p))) q

/-- Restriction is inverse image followed by the canonical comparison from
pulled-back ambient forms to relative forms on `Z`. -/
theorem restriction_spec (i : Z ⟶ X) (f : X ⟶ S) (p q : ℕ) :
    restriction i f p q =
      inverseImage i f p q ≫
        RingedSpace.moduleCohomologyMap
          ((Scheme.Modules.toRingedSpace X).map
            ((Scheme.Modules.pushforward i).map
              (pullbackFormToClosedForm i f p))) q := sorry

/-- The map on degree-`q` cohomology induced by the closed-immersion
Gysin morphism in form degree `p`. -/
noncomputable def cohomologyMap (i : Z ⟶ X) [IsClosedImmersion i]
    [Scheme.Hom.FinitePresentation i] (f : X ⟶ S) (c p q : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank c (Scheme.Hom.conormalSheaf i)] :
    RingedSpace.moduleCohomology
          ((Scheme.Modules.toRingedSpace X).obj
            ((Scheme.Modules.pushforward i).obj
              (sheaf Z.𝒪 Ω[(i ≫ f).toShHom] p))) q ⟶
      RingedSpace.moduleCohomology
        ((Scheme.Hom.LocalCohomology.functor i c).obj
          (relativeFormQCoh f (p + c))) q :=
  RingedSpace.moduleCohomologyMap (mapOfClosedImmersion i f c p) q

/-- The Gysin cohomology map is the cohomology morphism induced by
`mapOfClosedImmersion`. -/
theorem cohomologyMap_spec (i : Z ⟶ X) [IsClosedImmersion i]
    [Scheme.Hom.FinitePresentation i] (f : X ⟶ S) (c p q : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank c (Scheme.Hom.conormalSheaf i)] :
    cohomologyMap i f c p q =
      RingedSpace.moduleCohomologyMap (mapOfClosedImmersion i f c p) q := sorry

/-- Restriction maps preserve the constant unit defining the degree-zero
relative-form section. -/
theorem relativeFormZeroOneSection_naturality (f : X ⟶ S)
    {U V : (Opens X)ᵒᵖ} (r : U ⟶ V) :
    ((RingedSpace.DeRham.form f.toLRSHom.toShHom 0).val.map r).hom
        (SheafOfModules.RingedSite.DeRham.basicForm
          (RingedSpace.DeRham.structureMap f.toLRSHom.toShHom) 0 U 1
          (fun k ↦ Fin.elim0 k)) =
      SheafOfModules.RingedSite.DeRham.basicForm
        (RingedSpace.DeRham.structureMap f.toLRSHom.toShHom) 0 V 1
        (fun k ↦ Fin.elim0 k) := sorry

/-- The canonical global unit section of the degree-zero relative-form sheaf. -/
noncomputable def relativeFormZeroOneSection (f : X ⟶ S) :
    (RingedSpace.DeRham.form f.toLRSHom.toShHom 0).val.sections :=
  PresheafOfModules.sectionsMk
    (fun U ↦ SheafOfModules.RingedSite.DeRham.basicForm
      (RingedSpace.DeRham.structureMap f.toLRSHom.toShHom) 0 U 1
      (fun k ↦ Fin.elim0 k))
    (fun {_ _} r ↦ relativeFormZeroOneSection_naturality f r)

/-- The unit section as a class in degree-zero Hodge cohomology. -/
noncomputable def relativeFormZeroOneCohomology (f : X ⟶ S) :
    RingedSpace.moduleCohomology
      ((Scheme.Modules.toRingedSpace X).obj (sheaf X.𝒪 Ω[f.toShHom] 0)) 0 :=
  (CategoryTheory.Sheaf.cohomologyZeroEquivSections
    (Opens.grothendieckTopology X.carrier)
      ((SheafOfModules.toSheaf X.toRingedSpace.ringCatSheaf).obj
      ((Scheme.Modules.toRingedSpace X).obj (sheaf X.𝒪 Ω[f.toShHom] 0)))
    (⊤ : X.Opens)).symm
      (((formToExterior f 0).val.app (op (⊤ : X.Opens))).hom
        ((relativeFormZeroOneSection f).1 (op (⊤ : X.Opens))))

/-- The degree-zero Hodge cohomology unit is the class corresponding to the
canonical constant-one section. -/
theorem relativeFormZeroOneCohomology_spec (f : X ⟶ S) :
    relativeFormZeroOneCohomology f =
      (CategoryTheory.Sheaf.cohomologyZeroEquivSections
        (Opens.grothendieckTopology X.carrier)
        ((SheafOfModules.toSheaf X.toRingedSpace.ringCatSheaf).obj
          ((Scheme.Modules.toRingedSpace X).obj
            (sheaf X.𝒪 Ω[f.toShHom] 0)))
        (⊤ : X.Opens)).symm
          (((formToExterior f 0).val.app (op (⊤ : X.Opens))).hom
            ((relativeFormZeroOneSection f).1 (op (⊤ : X.Opens)))) := sorry

/-- The supported fundamental class `γ⁰(1)`, obtained by restricting the
degree-zero unit and applying the degree-zero Gysin cohomology map. -/
noncomputable def fundamentalClassOne (i : Z ⟶ X) [IsClosedImmersion i]
    [Scheme.Hom.FinitePresentation i] (f : X ⟶ S) (c : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank c (Scheme.Hom.conormalSheaf i)] :
    RingedSpace.moduleCohomology
      ((Scheme.Hom.LocalCohomology.functor i c).obj
        (relativeFormQCoh f (0 + c))) 0 :=
  (cohomologyMap i f c 0 0).hom
    ((restriction i f 0 0).hom (relativeFormZeroOneCohomology f))

/-- The class `fundamentalClassOne` is the Gysin image of the restricted
degree-zero unit. -/
theorem fundamentalClassOne_spec (i : Z ⟶ X) [IsClosedImmersion i]
    [Scheme.Hom.FinitePresentation i] (f : X ⟶ S) (c : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank c (Scheme.Hom.conormalSheaf i)] :
    fundamentalClassOne i f c =
      (cohomologyMap i f c 0 0).hom
        ((restriction i f 0 0).hom (relativeFormZeroOneCohomology f)) := sorry

/-- The direct conormal-duality map that wedges an inverse-image ambient
`p`-form with the top conormal form before applying the fundamental class. -/
noncomputable def inverseImageToFundamentalSource
    (i : Z ⟶ X) (f : X ⟶ S) (c p : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank c (Scheme.Hom.conormalSheaf i)] :
    (Scheme.Modules.pullback i).obj (sheaf X.𝒪 Ω[f.toShHom] p) ⟶
      (ihom (sheaf Z.𝒪 (Scheme.Hom.conormalSheaf i) c)).obj
          (SheafOfModules.unit Z.ringCatSheaf) ⊗
        (Scheme.Modules.pullback i).obj (sheaf X.𝒪 Ω[f.toShHom] (p + c)) :=
  pullbackFormComparison i f p ≫
    MonoidalClosed.curry (determinantWedgeForm i f c p) ≫
    @inv _ _ _ _ (MonoidalClosed.Dual.tensorComparison
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

/-- The inverse-image-to-fundamental-source map is the explicit composite of
pullback comparison, conormal wedge, duality comparison, and tensor symmetry. -/
theorem inverseImageToFundamentalSource_spec
    (i : Z ⟶ X) (f : X ⟶ S) (c p : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank c (Scheme.Hom.conormalSheaf i)] :
    inverseImageToFundamentalSource i f c p =
      pullbackFormComparison i f p ≫
        MonoidalClosed.curry (determinantWedgeForm i f c p) ≫
        @inv _ _ _ _ (MonoidalClosed.Dual.tensorComparison
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
            (SheafOfModules.unit Z.ringCatSheaf))).hom := sorry

/-- The sheaf morphism realizing `i⁻¹α ∧ γ⁰(1)`: pull back the ambient
form, wedge through conormal duality, and apply the fundamental class. -/
noncomputable def wedgeFundamentalClassSheafMap
    (i : Z ⟶ X) [IsClosedImmersion i]
    [Scheme.Hom.FinitePresentation i] (f : X ⟶ S) (c p : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank c (Scheme.Hom.conormalSheaf i)] :
    (Scheme.Modules.toRingedSpace X).obj (sheaf X.𝒪 Ω[f.toShHom] p) ⟶
      (Scheme.Hom.LocalCohomology.functor i c).obj
        (relativeFormQCoh f (p + c)) :=
  (Scheme.Modules.toRingedSpace X).map
      ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app
          (sheaf X.𝒪 Ω[f.toShHom] p) ≫
        (Scheme.Modules.pushforward i).map
          (inverseImageToFundamentalSource i f c p)) ≫
    (fundamentalClass i c).app (relativeFormQCoh f (p + c))

/-- The wedge-with-fundamental-class sheaf map is inverse image followed by
the conormal wedge construction and the local-cohomology fundamental class. -/
theorem wedgeFundamentalClassSheafMap_spec
    (i : Z ⟶ X) [IsClosedImmersion i]
    [Scheme.Hom.FinitePresentation i] (f : X ⟶ S) (c p : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank c (Scheme.Hom.conormalSheaf i)] :
    wedgeFundamentalClassSheafMap i f c p =
      (Scheme.Modules.toRingedSpace X).map
          ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app
              (sheaf X.𝒪 Ω[f.toShHom] p) ≫
            (Scheme.Modules.pushforward i).map
              (inverseImageToFundamentalSource i f c p)) ≫
        (fundamentalClass i c).app (relativeFormQCoh f (p + c)) := sorry

/-- The cohomological operation `α ↦ i⁻¹α ∧ γ⁰(1)`, induced by the
canonical inverse-image, wedge, conormal-duality, and fundamental-class map. -/
noncomputable def wedgeFundamentalClass
    (i : Z ⟶ X) [IsClosedImmersion i]
    [Scheme.Hom.FinitePresentation i] (f : X ⟶ S) (c p q : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank c (Scheme.Hom.conormalSheaf i)] :
    RingedSpace.moduleCohomology
          ((Scheme.Modules.toRingedSpace X).obj (sheaf X.𝒪 Ω[f.toShHom] p)) q ⟶
      RingedSpace.moduleCohomology
        ((Scheme.Hom.LocalCohomology.functor i c).obj
          (relativeFormQCoh f (p + c))) q :=
  RingedSpace.moduleCohomologyMap
    (wedgeFundamentalClassSheafMap i f c p) q

/-- The wedge-with-fundamental-class operation is induced by the explicit
sheaf morphism `wedgeFundamentalClassSheafMap`. -/
theorem wedgeFundamentalClass_spec
    (i : Z ⟶ X) [IsClosedImmersion i]
    [Scheme.Hom.FinitePresentation i] (f : X ⟶ S) (c p q : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank c (Scheme.Hom.conormalSheaf i)] :
    wedgeFundamentalClass i f c p q =
      RingedSpace.moduleCohomologyMap
        (wedgeFundamentalClassSheafMap i f c p) q := sorry

/-- Applying the Gysin cohomology map after restriction is the canonical
wedge-with-fundamental-class map. -/
theorem cohomologyMap_comp_restriction
    (i : Z ⟶ X) [IsClosedImmersion i]
    [Scheme.Hom.FinitePresentation i] (f : X ⟶ S) (c p q : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank c (Scheme.Hom.conormalSheaf i)] :
    restriction i f p q ≫ cohomologyMap i f c p q =
      wedgeFundamentalClass i f c p q := sorry

/-- The Gysin image of a restricted relative-form cohomology class is its
inverse image wedged with the degree-zero supported fundamental class. -/
theorem cohomologyMap_restriction
    (i : Z ⟶ X) [IsClosedImmersion i]
    [Scheme.Hom.FinitePresentation i] (f : X ⟶ S) (c p q : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank c (Scheme.Hom.conormalSheaf i)]
    (α : RingedSpace.moduleCohomology
      ((Scheme.Modules.toRingedSpace X).obj (sheaf X.𝒪 Ω[f.toShHom] p)) q) :
    (cohomologyMap i f c p q).hom ((restriction i f p q).hom α) =
      (wedgeFundamentalClass i f c p q).hom α := sorry

/-- Derived local cohomology of the relative-form sheaf, supported on the closed image of
`i : Z ⟶ X`. -/
noncomputable def supportedDerived (i : Z ⟶ X) [IsClosedImmersion i]
    (f : X ⟶ S) (n : ℕ) : RingedSpace.ModuleDerived X.toRingedSpace :=
  (inclusion X.toRingedSpace.ringCatSheaf i.ker.support).obj
    ((coreflector X.toRingedSpace.ringCatSheaf i.ker.support).obj
      ((ModuleCech.moduleToDerived X).obj
        ((Scheme.QCoh.inclusion X).obj (relativeFormQCoh f n))))

/-- The supported-derived relative-form object is the ambient image of the canonical
closed-support coreflector. -/
theorem supportedDerived_obj (i : Z ⟶ X) [IsClosedImmersion i]
    (f : X ⟶ S) (n : ℕ) :
    supportedDerived i f n =
      (inclusion X.toRingedSpace.ringCatSheaf i.ker.support).obj
        ((coreflector X.toRingedSpace.ringCatSheaf i.ker.support).obj
          ((ModuleCech.moduleToDerived X).obj
            ((Scheme.QCoh.inclusion X).obj (relativeFormQCoh f n)))) := rfl

/-- Degree-`c` local cohomology is canonically the degree-`c` cohomology sheaf of the
supported-derived relative-form object. -/
noncomputable def supportedDerivedCohomologyIso (i : Z ⟶ X) [IsClosedImmersion i]
    (f : X ⟶ S) (p c : ℕ) :
    (Scheme.Hom.LocalCohomology.functor i c).obj (relativeFormQCoh f (p + c)) ≅
      RingedSpace.ModuleDerived.cohomologySheaf (supportedDerived i f (p + c)) (c : ℤ) :=
  ((ExactFunctor.of (SheafOfModules.ClosedSubset.pushforward
    X.toRingedSpace.ringCatSheaf i.ker.support)).homologyFunctorIso (c : ℤ)).symm.app
      ((SheafOfModules.ClosedSubset.Derived.sectionsWithSupport
        X.toRingedSpace.ringCatSheaf i.ker.support).obj
          ((ModuleCech.moduleToDerived X).obj
            ((Scheme.QCoh.inclusion X).obj (relativeFormQCoh f (p + c)))))

/-- The degree-`c` supported-cohomology comparison is the exact-pushforward homology
comparison. -/
theorem supportedDerivedCohomologyIso_hom (i : Z ⟶ X) [IsClosedImmersion i]
    (f : X ⟶ S) (p c : ℕ) :
    (supportedDerivedCohomologyIso i f p c).hom =
      ((ExactFunctor.of (SheafOfModules.ClosedSubset.pushforward
        X.toRingedSpace.ringCatSheaf i.ker.support)).homologyFunctorIso (c : ℤ)).inv.app
        ((SheafOfModules.ClosedSubset.Derived.sectionsWithSupport
          X.toRingedSpace.ringCatSheaf i.ker.support).obj
            ((ModuleCech.moduleToDerived X).obj
              ((Scheme.QCoh.inclusion X).obj (relativeFormQCoh f (p + c))))) := sorry

/-- The lower bound on supported derived local cohomology is equivalent to vanishing of its
nonnegative local-cohomology sheaves strictly below `c`. -/
theorem supportedDerived_isGE_iff (i : Z ⟶ X) [IsClosedImmersion i]
    (f : X ⟶ S) (p c : ℕ) :
    (supportedDerived i f (p + c)).IsGE (c : ℤ) ↔
      ∀ j : ℕ, j < c →
        IsZero ((Scheme.Hom.LocalCohomology.functor i j).obj
          (relativeFormQCoh f (p + c))) := sorry

/-- Smooth relative forms and a Koszul-regular closed immersion give the canonical lower
cohomological bound required for the Gysin construction. -/
theorem supportedDerivedRelativeFormIsGEOfSmoothOfKoszulRegular
    (i : Z ⟶ X) [IsClosedImmersion i] [Scheme.Hom.FinitePresentation i]
    (f : X ⟶ S) [Smooth f] [IsKoszulRegularImmersion i] (p c : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank c (Scheme.Hom.conormalSheaf i)] :
    (supportedDerived i f (p + c)).IsGE (c : ℤ) := sorry

/-- The sheaf-level Gysin morphism, placed in degree `c`, followed by the canonical inclusion
of the lowest nonzero cohomology sheaf into supported derived local cohomology. -/
noncomputable def lowestDegreeMap (i : Z ⟶ X) [IsClosedImmersion i]
    [Scheme.Hom.FinitePresentation i] (f : X ⟶ S) (p c : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank c (Scheme.Hom.conormalSheaf i)]
    [(supportedDerived i f (p + c)).IsGE (c : ℤ)] :
    (DerivedCategory.singleFunctor X.toRingedSpace.Modules (c : ℤ)).obj
        ((Scheme.Modules.toRingedSpace X).obj
          ((Scheme.Modules.pushforward i).obj
            (sheaf Z.𝒪 Ω[(i ≫ f).toShHom] p))) ⟶
      supportedDerived i f (p + c) :=
  (DerivedCategory.singleFunctor X.toRingedSpace.Modules (c : ℤ)).map
      (mapOfClosedImmersion i f c p ≫
        (supportedDerivedCohomologyIso i f p c).hom) ≫
    RingedSpace.ModuleDerived.Cohomology.lowerCohomologyInclusion
      (supportedDerived i f (p + c)) (c : ℤ) inferInstance

/-- The lowest-degree Gysin map is the degree-`c` image of `mapOfClosedImmersion`, followed by
the canonical lower-cohomology inclusion. -/
theorem lowestDegreeMap_eq (i : Z ⟶ X) [IsClosedImmersion i]
    [Scheme.Hom.FinitePresentation i] (f : X ⟶ S) (p c : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank c (Scheme.Hom.conormalSheaf i)]
    [(supportedDerived i f (p + c)).IsGE (c : ℤ)] :
    lowestDegreeMap i f p c =
      (DerivedCategory.singleFunctor X.toRingedSpace.Modules (c : ℤ)).map
          (mapOfClosedImmersion i f c p ≫
            (supportedDerivedCohomologyIso i f p c).hom) ≫
        RingedSpace.ModuleDerived.Cohomology.lowerCohomologyInclusion
          (supportedDerived i f (p + c)) (c : ℤ) inferInstance := sorry

/-- The derived Gysin morphism on the pushforward sheaf, obtained from the lowest supported
cohomology and the coreflection counit. -/
noncomputable def derivedMapOnPushforward (i : Z ⟶ X) [IsClosedImmersion i]
    [Scheme.Hom.FinitePresentation i] (f : X ⟶ S) (p c : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank c (Scheme.Hom.conormalSheaf i)]
    [(supportedDerived i f (p + c)).IsGE (c : ℤ)] :
    (DerivedCategory.singleFunctor X.toRingedSpace.Modules (c : ℤ)).obj
        ((Scheme.Modules.toRingedSpace X).obj
          ((Scheme.Modules.pushforward i).obj
            (sheaf Z.𝒪 Ω[(i ≫ f).toShHom] p))) ⟶
      (ModuleCech.moduleToDerived X).obj
        ((Scheme.QCoh.inclusion X).obj (relativeFormQCoh f (p + c))) :=
  lowestDegreeMap i f p c ≫
    (adjunction X.toRingedSpace.ringCatSheaf i.ker.support).counit.app
      ((ModuleCech.moduleToDerived X).obj
        ((Scheme.QCoh.inclusion X).obj (relativeFormQCoh f (p + c))))

/-- The pushforward-sheaf presentation of the derived Gysin morphism factors through supported
derived local cohomology and its adjunction counit. -/
theorem derivedMapOnPushforward_eq (i : Z ⟶ X) [IsClosedImmersion i]
    [Scheme.Hom.FinitePresentation i] (f : X ⟶ S) (p c : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank c (Scheme.Hom.conormalSheaf i)]
    [(supportedDerived i f (p + c)).IsGE (c : ℤ)] :
    derivedMapOnPushforward i f p c = lowestDegreeMap i f p c ≫
      (adjunction X.toRingedSpace.ringCatSheaf i.ker.support).counit.app
        ((ModuleCech.moduleToDerived X).obj
          ((Scheme.QCoh.inclusion X).obj (relativeFormQCoh f (p + c)))) := sorry

/-- Derived pushforward along a closed immersion sends an object concentrated in degree `c`
to the pushforward sheaf concentrated in degree `c`. -/
noncomputable def pushforwardSingleIso (i : Z ⟶ X) [IsClosedImmersion i]
    (F : Z.Modules) (c : ℤ) :
    (RingedSpace.moduleDerivedPushforward i.toShHom).obj
        ((DerivedCategory.singleFunctor Z.toRingedSpace.Modules c).obj
          ((Scheme.Modules.toRingedSpace Z).obj F)) ≅
      (DerivedCategory.singleFunctor X.toRingedSpace.Modules c).obj
        ((Scheme.Modules.toRingedSpace X).obj ((Scheme.Modules.pushforward i).obj F)) := by
  -- Local instance justification (proof-local temporary data): canonical exactness supplies finite-limit preservation while constructing this derived comparison.
  letI : PreservesFiniteLimits (RingedSpace.Hom.pushforward i.toShHom) :=
    AlgebraicGeometry.RingedSpace.IsClosedImmersion.pushforwardExact.1
  -- Local instance justification (proof-local temporary data): canonical exactness supplies finite-colimit preservation while constructing this derived comparison.
  letI : PreservesFiniteColimits (RingedSpace.Hom.pushforward i.toShHom) :=
    AlgebraicGeometry.RingedSpace.IsClosedImmersion.pushforwardExact.2
  exact (CategoryTheory.Functor.RightDerived.Exact.homotopyIso
      (RingedSpace.Hom.pushforward i.toShHom)).symm.app _ ≪≫
    ((RingedSpace.Hom.pushforward i.toShHom).mapDerivedCategorySingleFunctor c).app _

/-- The forward map of `pushforwardSingleIso` first identifies total derived pushforward with
exact derived pushforward and then uses its single-object comparison. -/
theorem pushforwardSingleIso_hom (i : Z ⟶ X) [IsClosedImmersion i]
    (F : Z.Modules) (c : ℤ) :
    (pushforwardSingleIso i F c).hom =
      (CategoryTheory.Functor.RightDerived.Exact.homotopyIso
          (RingedSpace.Hom.pushforward i.toShHom)).inv.app _ ≫
        ((RingedSpace.Hom.pushforward i.toShHom).mapDerivedCategorySingleFunctor c).hom.app _ := sorry

/-- The derived Gysin morphism from the shifted relative-form sheaf on `Z` to the ambient
relative-form sheaf on `X`. -/
noncomputable def derivedMap (i : Z ⟶ X) [IsClosedImmersion i]
    [Scheme.Hom.FinitePresentation i] (f : X ⟶ S) (p c : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank c (Scheme.Hom.conormalSheaf i)]
    [(supportedDerived i f (p + c)).IsGE (c : ℤ)] :
    (RingedSpace.moduleDerivedPushforward i.toShHom).obj
        ((DerivedCategory.singleFunctor Z.toRingedSpace.Modules (c : ℤ)).obj
          ((Scheme.Modules.toRingedSpace Z).obj
            (sheaf Z.𝒪 Ω[(i ≫ f).toShHom] p))) ⟶
      (ModuleCech.moduleToDerived X).obj
        ((Scheme.QCoh.inclusion X).obj (relativeFormQCoh f (p + c))) :=
  (pushforwardSingleIso i (sheaf Z.𝒪 Ω[(i ≫ f).toShHom] p) (c : ℤ)).hom ≫
    derivedMapOnPushforward i f p c

/-- The derived Gysin morphism is exact pushforward of the shifted source followed by the
pushforward-sheaf construction. -/
theorem derivedMap_eq (i : Z ⟶ X) [IsClosedImmersion i]
    [Scheme.Hom.FinitePresentation i] (f : X ⟶ S) (p c : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank c (Scheme.Hom.conormalSheaf i)]
    [(supportedDerived i f (p + c)).IsGE (c : ℤ)] :
    derivedMap i f p c =
      (pushforwardSingleIso i (sheaf Z.𝒪 Ω[(i ≫ f).toShHom] p) (c : ℤ)).hom ≫
        derivedMapOnPushforward i f p c := sorry

/-- The cohomological Gysin map, with the source cohomology on `Z` restricted to the
global-section ring of `X`. The source is represented by placing `Ω^p_{Z/S}` in degree `c`
and taking cohomology in degree `q + c`. -/
noncomputable def hodgeCohomologyMap (i : Z ⟶ X) [IsClosedImmersion i]
    [Scheme.Hom.FinitePresentation i] (f : X ⟶ S) (p q c : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank c (Scheme.Hom.conormalSheaf i)]
    [(supportedDerived i f (p + c)).IsGE (c : ℤ)] :
    (DerivedCategory.homologyFunctor
          (ModuleCat (RingedSpace.globalSectionsRing X.toRingedSpace)) (q + c : ℤ)).obj
        ((RingedSpace.moduleSectionsRestrictionDerived i.toShHom ⊤).obj
          ((RingedSpace.Module.Derived.GlobalSections.functor Z.toRingedSpace).obj
            ((DerivedCategory.singleFunctor Z.toRingedSpace.Modules (c : ℤ)).obj
              ((Scheme.Modules.toRingedSpace Z).obj
                (sheaf Z.𝒪 Ω[(i ≫ f).toShHom] p))))) ⟶
      (DerivedCategory.homologyFunctor
          (ModuleCat (RingedSpace.globalSectionsRing X.toRingedSpace)) (q + c : ℤ)).obj
        ((RingedSpace.Module.Derived.GlobalSections.functor X.toRingedSpace).obj
          ((ModuleCech.moduleToDerived X).obj
            ((Scheme.QCoh.inclusion X).obj (relativeFormQCoh f (p + c))))) :=
  (DerivedCategory.homologyFunctor
      (ModuleCat (RingedSpace.globalSectionsRing X.toRingedSpace)) (q + c : ℤ)).map
    ((RingedSpace.Module.Derived.GlobalSections.pushforwardIso i.toShHom).hom.app
        ((DerivedCategory.singleFunctor Z.toRingedSpace.Modules (c : ℤ)).obj
          ((Scheme.Modules.toRingedSpace Z).obj
            (sheaf Z.𝒪 Ω[(i ≫ f).toShHom] p))) ≫
      (RingedSpace.Module.Derived.GlobalSections.functor X.toRingedSpace).map
        (derivedMap i f p c))

/-- The cohomological Gysin map determined by a smooth ambient morphism and a
Koszul-regular finitely presented closed immersion. -/
noncomputable def hodgeCohomologyMapOfSmoothOfKoszulRegular
    (i : Z ⟶ X) [IsClosedImmersion i] [Scheme.Hom.FinitePresentation i]
    (f : X ⟶ S) [Smooth f] [IsKoszulRegularImmersion i] (p q c : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank c (Scheme.Hom.conormalSheaf i)] :
    (DerivedCategory.homologyFunctor
          (ModuleCat (RingedSpace.globalSectionsRing X.toRingedSpace)) (q + c : ℤ)).obj
        ((RingedSpace.moduleSectionsRestrictionDerived i.toShHom ⊤).obj
          ((RingedSpace.Module.Derived.GlobalSections.functor Z.toRingedSpace).obj
            ((DerivedCategory.singleFunctor Z.toRingedSpace.Modules (c : ℤ)).obj
              ((Scheme.Modules.toRingedSpace Z).obj
                (sheaf Z.𝒪 Ω[(i ≫ f).toShHom] p))))) ⟶
      (DerivedCategory.homologyFunctor
          (ModuleCat (RingedSpace.globalSectionsRing X.toRingedSpace)) (q + c : ℤ)).obj
        ((RingedSpace.Module.Derived.GlobalSections.functor X.toRingedSpace).obj
          ((ModuleCech.moduleToDerived X).obj
            ((Scheme.QCoh.inclusion X).obj (relativeFormQCoh f (p + c))))) :=
  @hodgeCohomologyMap _ _ _ i _ _ f p q c _
    (supportedDerivedRelativeFormIsGEOfSmoothOfKoszulRegular i f p c)

/-- The cohomological Gysin map is obtained from the derived Gysin morphism by the canonical
pushforward comparison for derived global sections and degree-`q + c` cohomology. -/
theorem hodgeCohomologyMap_eq (i : Z ⟶ X) [IsClosedImmersion i]
    [Scheme.Hom.FinitePresentation i] (f : X ⟶ S) (p q c : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank c (Scheme.Hom.conormalSheaf i)]
    [(supportedDerived i f (p + c)).IsGE (c : ℤ)] :
    hodgeCohomologyMap i f p q c =
      (DerivedCategory.homologyFunctor
        (ModuleCat (RingedSpace.globalSectionsRing X.toRingedSpace)) (q + c : ℤ)).map
        ((RingedSpace.Module.Derived.GlobalSections.pushforwardIso i.toShHom).hom.app
            ((DerivedCategory.singleFunctor Z.toRingedSpace.Modules (c : ℤ)).obj
              ((Scheme.Modules.toRingedSpace Z).obj
                (sheaf Z.𝒪 Ω[(i ≫ f).toShHom] p))) ≫
          (RingedSpace.Module.Derived.GlobalSections.functor X.toRingedSpace).map
            (derivedMap i f p c)) := sorry

end Scheme.DeRham.Gysin
end AlgebraicGeometry

end
