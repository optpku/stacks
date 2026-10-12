/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.DeRham.DifferentialGradedAlgebra
public import ReasLib.AlgebraicGeometry.Scheme.DeRham.DerivedPushforward
public import ReasLib.AlgebraicGeometry.Scheme.DeRham.Cohomology.Pullback
public import ReasLib.AlgebraicGeometry.RingedSite.Module.GlobalSections.Additive
public import Mathlib.Algebra.Homology.ConcreteCategory
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module.Derived.Hypercohomology
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module.Homotopy.Shift
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module.UnitSection
public import ReasLib.Algebra.Homology.CochainDGAlgebra.HomologyZero
public import ReasLib.CategoryTheory.Pretriangulated.Functor.Localization.Lift
public import ReasLib.CategoryTheory.Shift.ShiftedHom.Functor
public import ReasLib.CategoryTheory.Functor.Derived.Total.Triangulated

@[expose] public section

/-!
# Action of relative de Rham cohomology classes

This file isolates the shifted endomorphism attached to a relative de Rham class, together with
its DG-module lift and the comparison maps used by restriction and derived direct image.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory ComplexShape
open AlgebraicGeometry RingedSite.Hom
open SheafOfModules.RingedSite
open scoped DifferentialGradedCategory
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra
open scoped SheafOfModules.RingedSite.DifferentialGradedModule
open scoped DerivedTensorProduct
open DerivedCategory.DerivedTensor.Right.Monoidal

noncomputable section
-- Local instance justification (defeq pin): the global-section unit uses the canonical derived category of the coefficient sheaf presentation.
attribute [local instance] SheafOfModules.RingedSite.moduleCategoryHasDerivedCategory
-- Local instance justification (instance diamond): the DG localization and shift comparisons must use the same intentionally non-global finite-biproduct instance fixed by the imported DG-derived API.
attribute [local instance] Abelian.hasFiniteBiproducts

universe u
namespace AlgebraicGeometry.Scheme.DeRham.ClassAction

open DerivedPushforward (derivedComplex)

variable {X S : Scheme.{u}} (p : X ⟶ S)

/-- The regular relative de Rham DG module in its intrinsic derived category. -/
noncomputable abbrev dgObject :=
  (SheafOfModules.RingedSite.DifferentialGradedModule.DerivedCategory.Q
    (deRhamDGA p)).obj
    (deRhamDGA p).regularModule

/-- The DG object is the localized regular module of the canonical relative de Rham DGA. -/
theorem dgObject_def : dgObject p =
    (SheafOfModules.RingedSite.DifferentialGradedModule.DerivedCategory.Q
      (deRhamDGA p)).obj (deRhamDGA p).regularModule := sorry

/-- The homotopy-level functor which forgets the de Rham action and localizes the underlying
cochain complex. -/
noncomputable abbrev forgetHomotopy :=
  SheafOfModules.RingedSite.DifferentialGradedModule.Homotopy.forget
      (deRhamDGA p) ⋙
    moduleLocalization.{u}
      (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom)

/-- Forgetting the de Rham action sends DG homotopy quasi-isomorphisms to isomorphisms in the
ordinary derived category. -/
theorem forgetHomotopy_inverts :
    (SheafOfModules.RingedSite.DifferentialGradedModule.Homotopy.quasiIso
      (deRhamDGA p)).IsInvertedBy
      (forgetHomotopy p) := sorry

/-- The derived functor which forgets the right de Rham DG-module structure. -/
noncomputable abbrev forget :
    SheafOfModules.RingedSite.DifferentialGradedModule.DerivedCategory.{u, u}
        (deRhamDGA p) ⥤
      ModuleDerived.{u}
        (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom) :=
  CategoryTheory.Localization.lift (forgetHomotopy p) (forgetHomotopy_inverts p)
    (SheafOfModules.RingedSite.DifferentialGradedModule.DerivedCategory.Qh (deRhamDGA p))

/-- The derived forgetful functor commutes with integer shifts. -/
noncomputable abbrev forgetCommShift : (forget p).CommShift ℤ :=
  CategoryTheory.Localization.liftCommShift
    (SheafOfModules.RingedSite.DifferentialGradedModule.Homotopy.quasiIso
      (deRhamDGA p))
    (SheafOfModules.RingedSite.DifferentialGradedModule.DerivedCategory.Qh
      (deRhamDGA p))
    (forgetHomotopy p) (forgetHomotopy_inverts p)

/-- Forgetting the localized regular de Rham DG module recovers the ordinary derived relative
de Rham complex. -/
noncomputable def dgObjectIso :
    (forget p).obj (dgObject p) ≅ derivedComplex p :=
  (SheafOfModules.RingedSite.DifferentialGradedModule.DerivedCategory.Localization.facIso
    (deRhamDGA p) (forgetHomotopy p) (forgetHomotopy_inverts p)).app
      ((SheafOfModules.RingedSite.DifferentialGradedModule.toK
        (deRhamDGA p)).obj (deRhamDGA p).regularModule)

/-- The derived-sections functor on relative de Rham DG modules after forgetting their action. -/
noncomputable abbrev derivedSections :=
  forget p ⋙
    moduleDerivedGlobalSections.{u}
      (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom)

/-- The additive forgetful functor followed by the canonical universe lift. -/
noncomputable abbrev cohomologyForgetLift :=
  forget₂ (coefficientModules p) AddCommGrpCat ⋙
    AddCommGrpCat.uliftFunctor.{u + 1, u}

/-- Hypercohomology of a derived de Rham DG module, obtained by forgetting the action, taking
derived global sections, and then taking cohomology. -/
noncomputable def hypercohomology (n : ℤ) :
    SheafOfModules.RingedSite.DifferentialGradedModule.DerivedCategory.{u, u}
        (deRhamDGA p) ⥤ AddCommGrpCat.{u + 1} :=
  derivedSections p ⋙
    DerivedCategory.homologyFunctor (coefficientModules p) n ⋙
    cohomologyForgetLift p

/-- Evaluating de Rham hypercohomology on the regular DG module recovers relative de Rham
cohomology. -/
noncomputable def cohomologyIso (n : ℤ) :
    (AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
        ((forget₂ (coefficientModules p) AddCommGrpCat).obj (cohomology p n)) ≅
      (hypercohomology p n).obj (dgObject p) :=
  ((moduleDerivedGlobalSections.{u}
        (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom) ⋙
      DerivedCategory.homologyFunctor (coefficientModules p) n ⋙
      forget₂ (coefficientModules p) AddCommGrpCat ⋙
      AddCommGrpCat.uliftFunctor.{u + 1, u}).mapIso (dgObjectIso p)).symm

/-- The underived complex of global sections of the relative de Rham complex. -/
noncomputable abbrev underivedSectionsComplex :=
  (@Functor.mapHomologicalComplex _ _ _ _ _ _ _
    (moduleGlobalSectionsFunctor.{u}
      (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom))
    (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _
      (moduleGlobalSectionsFunctor.{u}
        (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom))
      (moduleGlobalSectionsFunctor_additive.{u, u, u, u}
        (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom)))
    (up ℤ)).obj (extendedDeRhamComplex p)

/-- The local-section diagram of the structure module on the coefficient site. -/
noncomputable abbrev coefficientUnitSectionsDiagram :=
  moduleGlobalSectionsDiagram
    (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom)
    (unitModule
      (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom).siteTopology
      (RingedSpace.DeRham.coefficients p.toLRSHom.toShHom))

/-- Local unit sections of the structure module on the coefficient site are compatible with
restriction. -/
theorem coefficientUnitGlobalOne_naturality
    {U V : (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom)ᵒᵖ}
    (f : U ⟶ V) :
    ((coefficientUnitSectionsDiagram p).map f).hom
        (1 : (RingedSpace.DeRham.coefficients p.toLRSHom.toShHom).1.obj U) =
      (1 : (RingedSpace.DeRham.coefficients p.toLRSHom.toShHom).1.obj V) := sorry

/-- The compatible global unit of the structure module on the coefficient site. -/
noncomputable def coefficientUnitGlobalOne :
    ((moduleGlobalSectionsFunctor.{u}
      (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom)).obj
        (unitModule
          (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom).siteTopology
          (RingedSpace.DeRham.coefficients p.toLRSHom.toShHom))) :=
  (limit.isoLimitCone
    ⟨ModuleCat.HasLimits.limitCone (coefficientUnitSectionsDiagram p),
      ModuleCat.HasLimits.limitConeIsLimit (coefficientUnitSectionsDiagram p)⟩).inv.hom
    (equivShrink _
      ⟨fun U ↦ (1 : (RingedSpace.DeRham.coefficients p.toLRSHom.toShHom).1.obj U),
        fun f ↦ coefficientUnitGlobalOne_naturality p f⟩)

/-- Every local component of the compatible coefficient-site unit is one. -/
theorem coefficientUnitGlobalOne_π
    (U : (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom)ᵒᵖ) :
    (limit.π (coefficientUnitSectionsDiagram p) U).hom
        (coefficientUnitGlobalOne p) =
      (1 : (RingedSpace.DeRham.coefficients p.toLRSHom.toShHom).1.obj U) := sorry

/-- The constant-one section in degree zero of the underived global de Rham complex. -/
noncomputable def underivedOne :
    ((moduleGlobalSectionsFunctor.{u}
      (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom)).obj
        ((extendedDeRhamComplex p).X 0)) :=
  ((moduleGlobalSectionsFunctor.{u}
    (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom)).map
      (unitModuleToTensorUnit.{u, u, u} ≫ deRhamOne p)).hom
        (coefficientUnitGlobalOne p)

/-- The underived degree-zero unit is the canonical constant-one de Rham section. -/
theorem underivedOne_def : underivedOne p =
    ((moduleGlobalSectionsFunctor.{u}
      (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom)).map
        (unitModuleToTensorUnit.{u, u, u} ≫ deRhamOne p)).hom
          (coefficientUnitGlobalOne p) := sorry

/-- The constant-one global de Rham section is closed. -/
theorem underivedOne_closed :
    ((underivedSectionsComplex p).d 0 1).hom (underivedOne p) = 0 := sorry

/-- The degree-zero cycle represented by the constant-one global de Rham section. -/
noncomputable def underivedOneCycle : (underivedSectionsComplex p).cycles 0 :=
  (underivedSectionsComplex p).cyclesMk
    (underivedOne p) 1 CochainDGAlgebra.up_next_zero (underivedOne_closed p)

/-- The canonical unit cycle is represented by the constant-one section. -/
theorem underivedOneCycle_def :
    underivedOneCycle p = (underivedSectionsComplex p).cyclesMk
      (underivedOne p) 1 CochainDGAlgebra.up_next_zero (underivedOne_closed p) := sorry

/-- The degree-zero homology class of the constant-one global de Rham section before passage to
derived global sections. -/
noncomputable def underivedOneClass : (underivedSectionsComplex p).homology 0 :=
  ModuleCat.Hom.hom ((underivedSectionsComplex p).homologyπ 0)
    (underivedOneCycle p)

/-- The underived unit class is the homology image of the constant-one cycle. -/
theorem underivedOneClass_def :
    underivedOneClass p =
      ModuleCat.Hom.hom ((underivedSectionsComplex p).homologyπ 0)
        (underivedOneCycle p) := sorry

/-- The canonical unit in degree-zero relative de Rham cohomology, obtained from the strict
constant-one cycle through the total-right-derived global-sections unit. -/
noncomputable def cohomologyOneCanonical : cohomology p 0 :=
  -- Local instance justification (defeq pin): cochainUnit uses the additive proof of the specified moduleGlobalSectionsFunctor; this pin selects that same functor in its zero-morphism instance.
  letI : (moduleGlobalSectionsFunctor.{u}
      (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom)).Additive :=
    moduleGlobalSectionsFunctor_additive.{u, u, u, u}
      (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom)
  ((DerivedCategory.homologyFunctor (coefficientModules p) 0).map
    ((Functor.RightDerived.Homotopy.cochainUnit
      (moduleGlobalSectionsFunctor.{u}
        (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom))).app
          (extendedDeRhamComplex p))).hom
    (ModuleCat.Hom.hom
      ((DerivedCategory.homologyFunctorFactors (coefficientModules p) 0).inv.app
        (underivedSectionsComplex p)) (underivedOneClass p))

/-- The de Rham cohomology unit is the image of the strict constant-one class under the
total-right-derived global-sections unit. -/
theorem cohomologyOneCanonical_def :
    -- Local instance justification (defeq pin): match the same additive functor and cochainUnit instantiation used in cohomologyOneCanonical.
    letI : (moduleGlobalSectionsFunctor.{u}
        (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom)).Additive :=
      moduleGlobalSectionsFunctor_additive.{u, u, u, u}
        (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom)
    cohomologyOneCanonical p =
      ((DerivedCategory.homologyFunctor (coefficientModules p) 0).map
        ((Functor.RightDerived.Homotopy.cochainUnit
          (moduleGlobalSectionsFunctor.{u}
            (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom))).app
              (extendedDeRhamComplex p))).hom
        (ModuleCat.Hom.hom
          ((DerivedCategory.homologyFunctorFactors (coefficientModules p) 0).inv.app
            (underivedSectionsComplex p)) (underivedOneClass p)) := sorry

variable [(moduleDerivedGlobalSections.{u}
  (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom)).CommShift ℤ]

/-- The canonical shift comparison obtained from the shift compatibility of derived global
sections and the degreewise derived homology shift sequence. -/
noncomputable def shiftEquiv (n : ℤ) :
    hypercohomology p n ≅
      shiftFunctor
        (SheafOfModules.RingedSite.DifferentialGradedModule.DerivedCategory.{u, u}
          (deRhamDGA p)) n ⋙ hypercohomology p 0 :=
  Functor.isoWhiskerRight
    (((derivedSections p ⋙
      DerivedCategory.homologyFunctor (coefficientModules p) 0).isoShift n).symm)
    (cohomologyForgetLift p)

/-- The regular DG module's unit as a class in degree-zero hypercohomology. -/
noncomputable def regularHypercohomologyOneCanonical :
    (hypercohomology p 0).obj (dgObject p) :=
  (cohomologyIso p 0).hom (ULift.up (cohomologyOneCanonical p))

/-- The regular hypercohomology unit is the image of the canonical de Rham unit under the
regular-object comparison. -/
theorem regularHypercohomologyOneCanonical_def :
    regularHypercohomologyOneCanonical p =
      (cohomologyIso p 0).hom (ULift.up (cohomologyOneCanonical p)) := sorry

/-- Evaluation of a morphism out of the localized regular DG module on its canonical unit
class. -/
noncomputable def degreeZeroEvaluationFunction
    (M : SheafOfModules.RingedSite.DifferentialGradedModule.DerivedCategory.{u, u}
      (deRhamDGA p)) :
    (dgObject p ⟶ M) → (hypercohomology p 0).obj M :=
  fun φ ↦ ((hypercohomology p 0).map φ).hom (regularHypercohomologyOneCanonical p)

/-- Degree-zero unit evaluation preserves zero. -/
theorem degreeZeroEvaluationFunction_zero
    (M : SheafOfModules.RingedSite.DifferentialGradedModule.DerivedCategory.{u, u}
      (deRhamDGA p)) :
    degreeZeroEvaluationFunction p M 0 = 0 := sorry

/-- Degree-zero unit evaluation preserves addition. -/
theorem degreeZeroEvaluationFunction_add
    (M : SheafOfModules.RingedSite.DifferentialGradedModule.DerivedCategory.{u, u}
      (deRhamDGA p)) (f g : dgObject p ⟶ M) :
    degreeZeroEvaluationFunction p M (f + g) =
      degreeZeroEvaluationFunction p M f + degreeZeroEvaluationFunction p M g := sorry

/-- Evaluation on the regular unit as a morphism of additive groups. -/
noncomputable def degreeZeroEvaluationApp
    (M : SheafOfModules.RingedSite.DifferentialGradedModule.DerivedCategory.{u, u}
      (deRhamDGA p)) :
    (preadditiveCoyoneda.obj (Opposite.op (dgObject p))).obj M ⟶
      (hypercohomology p 0).obj M :=
  AddCommGrpCat.ofHom
    { toFun := degreeZeroEvaluationFunction p M
      map_zero' := degreeZeroEvaluationFunction_zero p M
      map_add' := degreeZeroEvaluationFunction_add p M }

/-- Evaluation on the regular unit is natural in the target DG module. -/
theorem degreeZeroEvaluation_naturality
    {M N : SheafOfModules.RingedSite.DifferentialGradedModule.DerivedCategory.{u, u}
      (deRhamDGA p)} (f : M ⟶ N) :
    (preadditiveCoyoneda.obj (Opposite.op (dgObject p))).map f ≫
        degreeZeroEvaluationApp p N =
      degreeZeroEvaluationApp p M ≫ (hypercohomology p 0).map f := sorry

/-- The natural unit-evaluation transformation from the regular representable functor to
degree-zero hypercohomology. -/
noncomputable def degreeZeroEvaluation :
    preadditiveCoyoneda.obj (Opposite.op (dgObject p)) ⟶ hypercohomology p 0 where
  app := degreeZeroEvaluationApp p
  naturality := fun {_ _} f ↦ degreeZeroEvaluation_naturality p f

/-- The proof-independent inverse function to canonical degree-zero unit evaluation. -/
noncomputable def degreeZeroActionFunction
    (M : SheafOfModules.RingedSite.DifferentialGradedModule.DerivedCategory.{u, u}
      (deRhamDGA p)) :
    (hypercohomology p 0).obj M → (dgObject p ⟶ M) :=
  Function.invFun (degreeZeroEvaluationFunction p M)

/-- The inverse unit-action function preserves zero. -/
theorem degreeZeroActionFunction_zero
    (M : SheafOfModules.RingedSite.DifferentialGradedModule.DerivedCategory.{u, u}
      (deRhamDGA p)) :
    degreeZeroActionFunction p M 0 = 0 := sorry

/-- The inverse unit-action function preserves addition. -/
theorem degreeZeroActionFunction_add
    (M : SheafOfModules.RingedSite.DifferentialGradedModule.DerivedCategory.{u, u}
      (deRhamDGA p)) (x y : (hypercohomology p 0).obj M) :
    degreeZeroActionFunction p M (x + y) =
      degreeZeroActionFunction p M x + degreeZeroActionFunction p M y := sorry

/-- The derived action induced by a degree-zero hypercohomology class, as an additive-group
morphism. -/
noncomputable def degreeZeroActionApp
    (M : SheafOfModules.RingedSite.DifferentialGradedModule.DerivedCategory.{u, u}
      (deRhamDGA p)) :
    (hypercohomology p 0).obj M ⟶
      (preadditiveCoyoneda.obj (Opposite.op (dgObject p))).obj M :=
  AddCommGrpCat.ofHom
    { toFun := degreeZeroActionFunction p M
      map_zero' := degreeZeroActionFunction_zero p M
      map_add' := degreeZeroActionFunction_add p M }

/-- The action induced by a degree-zero class is natural in the target DG module. -/
theorem degreeZeroAction_naturality
    {M N : SheafOfModules.RingedSite.DifferentialGradedModule.DerivedCategory.{u, u}
      (deRhamDGA p)} (f : M ⟶ N) :
    (hypercohomology p 0).map f ≫ degreeZeroActionApp p N =
      degreeZeroActionApp p M ≫
        (preadditiveCoyoneda.obj (Opposite.op (dgObject p))).map f := sorry

/-- The natural action transformation inverse to evaluation on the regular unit. -/
noncomputable def degreeZeroAction :
    hypercohomology p 0 ⟶
      preadditiveCoyoneda.obj (Opposite.op (dgObject p)) where
  app := degreeZeroActionApp p
  naturality := fun {_ _} f ↦ degreeZeroAction_naturality p f

/-- Acting by a degree-zero class and then evaluating on the unit is the identity. -/
theorem degreeZeroAction_evaluation :
    degreeZeroAction p ≫ degreeZeroEvaluation p = 𝟙 (hypercohomology p 0) := sorry

/-- Evaluating a regular-module morphism on the unit and acting by the result is the identity. -/
theorem degreeZeroEvaluation_action :
    degreeZeroEvaluation p ≫ degreeZeroAction p =
      𝟙 (preadditiveCoyoneda.obj (Opposite.op (dgObject p))) := sorry

/-- The canonical degree-zero representability equivalence. Its inverse is explicit evaluation
on the de Rham unit, and its forward map is the corresponding `UnitSection.action`. -/
noncomputable def degreeZeroEquiv : hypercohomology p 0 ≅
    preadditiveCoyoneda.obj (Opposite.op (dgObject p)) where
  hom := degreeZeroAction p
  inv := degreeZeroEvaluation p
  hom_inv_id := degreeZeroAction_evaluation p
  inv_hom_id := degreeZeroEvaluation_action p

/-- The inverse degree-zero representability map is evaluation on the canonical regular-module
unit class. -/
theorem degreeZeroEquiv_inv_app
    (M : SheafOfModules.RingedSite.DifferentialGradedModule.DerivedCategory.{u, u}
      (deRhamDGA p)) (f : dgObject p ⟶ M) :
    ((degreeZeroEquiv p).inv.app M).hom f = degreeZeroEvaluationFunction p M f := sorry

/-- The forward degree-zero representability map is characterized by evaluation on the regular
unit, and hence agrees with the derived form of `UnitSection.action`. -/
theorem degreeZeroEquiv_hom_app_spec
    (M : SheafOfModules.RingedSite.DifferentialGradedModule.DerivedCategory.{u, u}
      (deRhamDGA p)) (x : (hypercohomology p 0).obj M) :
    degreeZeroEvaluationFunction p M (((degreeZeroEquiv p).hom.app M).hom x) = x := sorry

/-- Applying derived global sections to an ordinary shifted endomorphism of the relative de Rham
complex. -/
noncomputable def globalize (n : ℤ)
    (φ : ShiftedHom (derivedComplex p) (derivedComplex p) n) :
    ShiftedHom (globalDerivedObject p) (globalDerivedObject p) n :=
  (moduleDerivedGlobalSections.{u}
      (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom)).shiftedHomMap
    (Iso.refl _) (Iso.refl _) n φ

/-- Evaluation of an ordinary shifted endomorphism on the canonical degree-zero de Rham unit. -/
noncomputable def ordinaryUnitEvaluation (n : ℤ)
    (φ : ShiftedHom (derivedComplex p) (derivedComplex p) n) : cohomology p n :=
  ((DerivedCategory.homologyFunctor (coefficientModules p) 0).shiftMap
    (globalize p n φ) 0 n (Int.add_zero n)).hom (cohomologyOneCanonical p)

/-- Evaluation of a DG-derived shifted endomorphism on the regular module's unit, after applying
the canonical forgetful and derived-global-sections functors. -/
noncomputable def unitEvaluation (n : ℤ)
    (ψ : ShiftedHom (dgObject p) (dgObject p) n) : cohomology p n :=
  ordinaryUnitEvaluation p n
    ((forget p).shiftedHomMap (dgObjectIso p) (dgObjectIso p) n ψ)

/-- DG unit evaluation is ordinary evaluation after forgetting the de Rham-module action. -/
theorem unitEvaluation_def (n : ℤ)
    (ψ : ShiftedHom (dgObject p) (dgObject p) n) :
    unitEvaluation p n ψ = ordinaryUnitEvaluation p n
      ((forget p).shiftedHomMap (dgObjectIso p) (dgObjectIso p) n ψ) := sorry

/-- Lifted unit evaluation preserves zero. -/
theorem unitEvaluationLift_zero (n : ℤ) :
    ULift.up (unitEvaluation p n 0) = 0 := sorry

/-- Lifted unit evaluation preserves addition. -/
theorem unitEvaluationLift_add (n : ℤ)
    (f g : ShiftedHom (dgObject p) (dgObject p) n) :
    ULift.up (unitEvaluation p n (f + g)) =
      ULift.up (unitEvaluation p n f) + ULift.up (unitEvaluation p n g) := sorry

/-- Unit evaluation as an additive map, with the target universe lifted to the morphism
universe of the DG derived category. -/
noncomputable def unitEvaluationAddHom (n : ℤ) :
    ShiftedHom (dgObject p) (dgObject p) n →+
      ULift.{u + 1, u} (cohomology p n) where
  toFun ψ := ULift.up (unitEvaluation p n ψ)
  map_zero' := unitEvaluationLift_zero p n
  map_add' := unitEvaluationLift_add p n

/-- Evaluation on the regular-module unit is bijective. -/
theorem unitEvaluation_bijective (n : ℤ) :
    Function.Bijective (unitEvaluationAddHom p n) := sorry

/-- The canonical representability equivalence between a relative de Rham class and its shifted
endomorphism of the localized regular DG module. -/
noncomputable def classEquiv (n : ℤ) :
    ULift.{u + 1, u} (cohomology p n) ≃+
      ShiftedHom (dgObject p) (dgObject p) n :=
  ((cohomologyIso p n) ≪≫
    SheafOfModules.RingedSite.DifferentialGradedModule.Hypercohomology.objIso
      (deRhamDGA p) (hypercohomology p) (shiftEquiv p) (degreeZeroEquiv p)
        (dgObject p) n).addCommGroupIsoToAddEquiv

/-- The forward class equivalence is the de Rham comparison followed by canonical
hypercohomology representability. -/
theorem classEquiv_apply (n : ℤ) (ξ : cohomology p n) :
    classEquiv p n (ULift.up ξ) =
      (SheafOfModules.RingedSite.DifferentialGradedModule.Hypercohomology.objIso
        (deRhamDGA p) (hypercohomology p) (shiftEquiv p) (degreeZeroEquiv p)
          (dgObject p) n).hom
          ((cohomologyIso p n).hom (ULift.up ξ)) := sorry

/-- The inverse of canonical hypercohomology representability is evaluation on the regular
de Rham unit. -/
theorem classEquiv_symm_apply (n : ℤ)
    (ψ : ShiftedHom (dgObject p) (dgObject p) n) :
    ULift.down ((classEquiv p n).symm ψ) = unitEvaluation p n ψ := sorry

/-- The right-DG-module lift of the shifted endomorphism attached to a relative de Rham class. -/
noncomputable def dgLift (n : ℤ) (ξ : cohomology p n) :
    ShiftedHom (dgObject p) (dgObject p) n :=
  classEquiv p n (ULift.up ξ)

/-- The DG lift is the image of the class under the specialized representability equivalence. -/
theorem dgLift_def (n : ℤ) (ξ : cohomology p n) :
    dgLift p n ξ = classEquiv p n (ULift.up ξ) := sorry

/-- The canonical shifted endomorphism of the ordinary relative de Rham complex attached to a
relative de Rham class. -/
noncomputable def map (n : ℤ) (ξ : cohomology p n) :
    ShiftedHom (derivedComplex p) (derivedComplex p) n :=
  (forget p).shiftedHomMap (dgObjectIso p) (dgObjectIso p) n
    (dgLift p n ξ)

/-- The class-action morphism is obtained by forgetting its concrete DG-module lift and
conjugating by the regular-complex comparison. -/
theorem map_eq_forget (n : ℤ) (ξ : cohomology p n) :
    map p n ξ =
      (forget p).shiftedHomMap (dgObjectIso p) (dgObjectIso p) n
        (dgLift p n ξ) := sorry

/-- Evaluation of a DG-derived shifted endomorphism on the regular module's unit. -/
noncomputable abbrev valueAtOne (n : ℤ)
    (ψ : ShiftedHom (dgObject p) (dgObject p) n) : cohomology p n :=
  unitEvaluation p n ψ

/-- Unit evaluation is the inverse hypercohomology representability map, followed by removal of
the universe lift. -/
theorem valueAtOne_eq_unitEvaluation (n : ℤ)
    (ψ : ShiftedHom (dgObject p) (dgObject p) n) :
    valueAtOne p n ψ = unitEvaluation p n ψ := sorry

/-- The canonical ordinary class action is the image of its displayed
right-DG-module lift. -/
theorem lifts (n : ℤ) (ξ : cohomology p n) :
    (forget p).shiftedHomMap (dgObjectIso p) (dgObjectIso p) n
        (dgLift p n ξ) = map p n ξ := sorry

/-- The DG lift evaluates on the unit section to the original de Rham class. -/
theorem one (n : ℤ) (ξ : cohomology p n) :
    valueAtOne p n (dgLift p n ξ) = ξ := sorry

/-- Liftability to a right DG-module map and evaluation on the unit uniquely characterize the
ordinary shifted class-action morphism. -/
theorem characterization (n : ℤ) (ξ : cohomology p n)
    (φ : ShiftedHom (derivedComplex p) (derivedComplex p) n) :
    φ = map p n ξ ↔
      ∃ ψ : ShiftedHom (dgObject p) (dgObject p) n,
        (forget p).shiftedHomMap (dgObjectIso p) (dgObjectIso p) n ψ = φ ∧
          valueAtOne p n ψ = ξ := sorry

/-- The shifted endomorphism obtained after applying derived global sections to a relative de
Rham class action. -/
noncomputable def globalMap (n : ℤ) (ξ : cohomology p n) :
    ShiftedHom (globalDerivedObject p) (globalDerivedObject p) n :=
  (moduleDerivedGlobalSections.{u}
      (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom)).shiftedHomMap
    (Iso.refl _) (Iso.refl _) n (map p n ξ)

/-- Derived global sections transport the ordinary class action through their shift
comparison. -/
theorem globalMap_def (n : ℤ) (ξ : cohomology p n) :
    globalMap p n ξ =
      (moduleDerivedGlobalSections.{u}
        (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom)).shiftedHomMap
          (Iso.refl _) (Iso.refl _) n (map p n ξ) := sorry

/-- The morphism on degree-`m` de Rham cohomology induced by the shifted class action. -/
noncomputable def onCohomology (n m : ℤ) (ξ : cohomology p n) :
    cohomology p m ⟶ cohomology p (n + m) :=
  (DerivedCategory.homologyFunctor (coefficientModules p) 0).shiftMap
    (globalMap p n ξ) m (n + m) rfl

/-- The induced cohomology morphism is the shift-sequence map of the derived-global-sections
endomorphism. -/
theorem onCohomology_def (n m : ℤ) (ξ : cohomology p n) :
    onCohomology p n m ξ =
      (DerivedCategory.homologyFunctor (coefficientModules p) 0).shiftMap
        (globalMap p n ξ) m (n + m) rfl := sorry



section Restriction

variable (U : X.Opens)
variable [(moduleDerivedGlobalSections.{u}
  (RingedSpace.DeRham.coefficientSite
    (U.ι ≫ p).toLRSHom.toShHom)).CommShift ℤ]

/-- The canonical square from an open subscheme to the ambient relative morphism. -/
theorem openSquare : CommSq U.ι (U.ι ≫ p) p (𝟙 S) := ⟨by simp⟩

/-- Direct image along the coefficient morphism of `openSquare` has its canonical total right
derived functor. -/
theorem openHasRightDerived : Functor.HasRightDerivedFunctor
    (modulePushforwardToDerived.{u} (Cohomology.coefficientHom (openSquare p U)))
    (ModuleQis.{u}
      (RingedSpace.DeRham.coefficientSite (U.ι ≫ p).toLRSHom.toShHom)) :=
  modulePushforwardToDerived.hasRightDerived (Cohomology.coefficientHom (openSquare p U))

-- Local instance justification (defeq pin): restriction formulas must use the derived functor at this specified coefficient morphism; openHasRightDerived is the existing general construction specialized to it.
attribute [local instance] openHasRightDerived

variable [(modulePushforwardDerived.{u}
  (Cohomology.coefficientHom (openSquare p U))).CommShift ℤ]

/-- The canonical restriction of a relative de Rham class to an open subscheme. -/
noncomputable def restrictedClass (n : ℤ) (ξ : cohomology p n) :
    cohomology (U.ι ≫ p) n :=
  (Cohomology.restrictedPullback (openSquare p U) n).hom ξ

/-- The restricted class is induced by the canonical cohomology pullback for the open square. -/
theorem restrictedClass_def (n : ℤ) (ξ : cohomology p n) :
    restrictedClass p U n ξ =
      (Cohomology.restrictedPullback (openSquare p U) n).hom ξ := sorry

/-- The DG-module lift of the class action attached to the canonically restricted class. -/
noncomputable def restrictedDgLift (n : ℤ) (ξ : cohomology p n) :
    ShiftedHom (dgObject (U.ι ≫ p)) (dgObject (U.ι ≫ p)) n :=
  dgLift (U.ι ≫ p) n (restrictedClass p U n ξ)

/-- The restricted DG lift is the canonical lift of the restricted de Rham class. -/
theorem restrictedDgLift_def (n : ℤ) (ξ : cohomology p n) :
    restrictedDgLift p U n ξ =
      dgLift (U.ι ≫ p) n (restrictedClass p U n ξ) := sorry

/-- The ordinary derived de Rham pullback associated to an open immersion. -/
noncomputable def ordinaryRestriction :
    derivedComplex p ⟶
      (modulePushforwardDerived.{u}
        (Cohomology.coefficientHom (openSquare p U))).obj
        (derivedComplex (U.ι ≫ p)) :=
  Cohomology.derivedPullback (openSquare p U)

/-- Ordinary restriction is the canonical derived pullback for the open square. -/
theorem ordinaryRestriction_def :
    ordinaryRestriction p U = Cohomology.derivedPullback (openSquare p U) := sorry

/-- The restricted class action after direct image to the ambient coefficient site. -/
noncomputable def restrictedMap (n : ℤ) (ξ : cohomology p n) :
    ShiftedHom
      ((modulePushforwardDerived.{u}
        (Cohomology.coefficientHom (openSquare p U))).obj
          (derivedComplex (U.ι ≫ p)))
      ((modulePushforwardDerived.{u}
        (Cohomology.coefficientHom (openSquare p U))).obj
          (derivedComplex (U.ι ≫ p))) n :=
  (modulePushforwardDerived.{u}
      (Cohomology.coefficientHom (openSquare p U))).shiftedHomMap
    (Iso.refl _) (Iso.refl _) n
      (map (U.ι ≫ p) n (restrictedClass p U n ξ))

/-- The restricted endomorphism is the derived direct image of the action of the restricted
class. -/
theorem restrictedMap_def (n : ℤ) (ξ : cohomology p n) :
    restrictedMap p U n ξ =
      (modulePushforwardDerived.{u}
        (Cohomology.coefficientHom (openSquare p U))).shiftedHomMap
          (Iso.refl _) (Iso.refl _) n
            (map (U.ι ≫ p) n (restrictedClass p U n ξ)) := sorry

/-- Restriction to an open subscheme commutes with the canonical class action. -/
theorem restrict (n : ℤ) (ξ : cohomology p n) :
    CommSq (map p n ξ) (ordinaryRestriction p U)
      ((shiftFunctor _ n).map (ordinaryRestriction p U))
      (restrictedMap p U n ξ) := sorry

end Restriction



end AlgebraicGeometry.Scheme.DeRham.ClassAction
