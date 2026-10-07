module

public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Homology.CochainComplex.DifferentialGraded.HomComplex.Derived.Over
public import ReasLib.Algebra.Homology.CochainComplex.DifferentialGraded.HomComplex.KInjective.Over
public import ReasLib.Algebra.Homology.CochainComplex.KInjective.Over
public import ReasLib.CategoryTheory.Preadditive.HomCongr

/-!
# Cohomology of explicit-base-ring derived Hom

This leaf gives the generic `R`-linear version of the K-injective Hom-cohomology representation.
It stops at the canonical model and comparison functors; the integral file is only a compatibility
facade for the `R := ℤ` case.
-/

@[expose] public section

noncomputable section

universe r u v w g

open CategoryTheory CategoryTheory.Limits DifferentialGradedCategory
open CategoryTheory.CochainComplex.Enriched.Over
open scoped DifferentialGradedCategory

namespace CategoryTheory.CochainComplex.Enriched.Over.RHom.Cohomology

variable {R : Type r} [CommRing R]
variable {C : Type u} [Category.{v} C] [Abelian C] [Linear R C]
variable [HasDerivedCategory.{w} C]

/-- The full subcategory of explicit-base-ring K-injective complexes. -/
@[stacks 0CS6 "explicit-base-ring K-injective Hom model category"]
abbrev Model :=
  (KInjective.property (R := R) (C := C)).FullSubcategory

/-- The product quasi-isomorphism system on pairs of explicit-base-ring K-injective models. -/
@[stacks 0CS6 "explicit-base-ring K-injective Hom denominators"]
abbrev modelQis : MorphismProperty
    ((Model (R := R) (C := C))ᵒᵖ × Model (R := R) (C := C)) :=
  (KInjective.qis (R := R) (C := C)).op.prod
    (KInjective.qis (R := R) (C := C))

/-- The product inclusion from K-injective models to the enriched homotopy category. -/
@[stacks 0CS6 "explicit-base-ring K-injective Hom model inclusion"]
abbrev modelInclusion :
    (Model (R := R) (C := C))ᵒᵖ × Model (R := R) (C := C) ⥤
      (DifferentialGradedCategory.K R (CochainComplex C ℤ))ᵒᵖ ×
        DifferentialGradedCategory.K R (CochainComplex C ℤ) :=
  (KInjective.property (R := R) (C := C)).ι.op.prod
    (KInjective.property (R := R) (C := C)).ι

/-- The product localization from K-injective models to pairs of derived objects. -/
@[stacks 0CS6 "explicit-base-ring K-injective Hom localization"]
noncomputable abbrev modelLocalization :
    (Model (R := R) (C := C))ᵒᵖ × Model (R := R) (C := C) ⥤
      (DerivedCategory.{w} C)ᵒᵖ × DerivedCategory.{w} C :=
  (KInjective.localization (R := R) (C := C)).op.prod
    (KInjective.localization (R := R) (C := C))

section DerivedHom

variable [RHom.Has (R := R) (C := C)]

/-- Degree-`n` cohomology of explicit-base-ring derived Hom. -/
@[stacks 0CS6 "explicit-base-ring derived Hom cohomology bifunctor"]
noncomputable abbrev functor (n : ℤ) :=
  RHom.functor (R := R) (C := C) ⋙
    DerivedCategory.homologyFunctor (ModuleCat.{v} R) n

/-- Degree-`n` cohomology of explicit-base-ring derived Hom in a common module universe. -/
@[stacks 0CS6 "lifted explicit-base-ring derived Hom cohomology"]
noncomputable abbrev uliftFunctor (n : ℤ) :
    (DerivedCategory.{w} C)ᵒᵖ × DerivedCategory.{w} C ⥤ ModuleCat.{max v w} R :=
  functor (R := R) (C := C) n ⋙ ModuleCat.uliftFunctor.{max v w} R

end DerivedHom

/-- The strict enriched Hom model restricted to K-injective pairs. -/
@[stacks 0CS6 "restricted explicit-base-ring derived Hom model"]
noncomputable abbrev modelHom :
    (Model (R := R) (C := C))ᵒᵖ × Model (R := R) (C := C) ⥤
      DerivedCategory.{max r (v + 1)} (ModuleCat.{v} R) :=
  modelInclusion (R := R) (C := C) ⋙ RHom.source (R := R) (C := C)

/-- Degree-`n` cohomology of the restricted strict Hom model. -/
@[stacks 0CS6 "restricted explicit-base-ring Hom cohomology model"]
noncomputable abbrev modelCohomology (n : ℤ) :
    (Model (R := R) (C := C))ᵒᵖ × Model (R := R) (C := C) ⥤ ModuleCat.{max v w} R :=
  modelHom (R := R) (C := C) ⋙
    DerivedCategory.homologyFunctor (ModuleCat.{v} R) n ⋙
      ModuleCat.uliftFunctor.{max v w} R

/-- Shifted derived Hom on the product of derived objects, lifted to the same module universe. -/
@[stacks 0CS6 "shifted explicit-base-ring derived Hom target"]
noncomputable abbrev shiftedFunctor (n : ℤ) :
    (DerivedCategory.{w} C)ᵒᵖ × DerivedCategory.{w} C ⥤ ModuleCat.{max v w} R :=
  Functor.uncurry.obj (ShiftedHom.linearCoyoneda R (DerivedCategory C) n) ⋙
    ModuleCat.uliftFunctor.{max v w} R

/-- The shifted-Hom target restricted to pairs of explicit-base-ring K-injective models. -/
@[stacks 0CS6 "explicit-base-ring shifted Hom model"]
noncomputable abbrev modelShifted (n : ℤ) :
    (Model (R := R) (C := C))ᵒᵖ × Model (R := R) (C := C) ⥤
      ModuleCat.{max v w} R :=
  modelLocalization (R := R) (C := C) ⋙ shiftedFunctor (R := R) (C := C) n

/-- Remove the common universe lift from strict Hom cohomology. -/
@[stacks 0CS6 "universe descent for explicit-base-ring Hom cohomology"]
noncomputable def modelCohomologyDown
    (X : (Model (R := R) (C := C))ᵒᵖ × Model (R := R) (C := C)) (n : ℤ) :
    (modelCohomology (R := R) (C := C) n).obj X ≃ₗ[R]
      (DerivedCategory.homologyFunctor (ModuleCat.{v} R) n).obj
        ((modelHom (R := R) (C := C)).obj X) :=
  ULift.moduleEquiv (R := R)
    (M := (DerivedCategory.homologyFunctor (ModuleCat.{v} R) n).obj
      ((modelHom (R := R) (C := C)).obj X))

/-- Derived homology of the strict Hom object agrees with ordinary Hom-complex cohomology. -/
@[stacks 0CS6 "strict explicit-base-ring Hom homology comparison"]
noncomputable def modelHomologyEquiv
    (X : (Model (R := R) (C := C))ᵒᵖ × Model (R := R) (C := C)) (n : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{v} R) n).obj
        ((modelHom (R := R) (C := C)).obj X) ≃ₗ[R]
      (homComplex (R := R) X.1.unop.obj.obj X.2.obj.obj).homology n :=
  ((DerivedCategory.homologyFunctorFactors (ModuleCat.{v} R) n).app
    (homComplex (R := R) X.1.unop.obj.obj X.2.obj.obj)).toLinearEquiv

/-- K-injectivity identifies strict Hom cohomology with shifted derived Hom. -/
@[stacks 0CS6 "K-injective explicit-base-ring Hom cohomology model"]
noncomputable def modelExtEquiv
    (X : (Model (R := R) (C := C))ᵒᵖ × Model (R := R) (C := C)) (n : ℤ) :
  (homComplex (R := R) X.1.unop.obj.obj X.2.obj.obj).homology n ≃ₗ[R]
      ShiftedHom (DerivedCategory.Q.obj X.1.unop.obj.obj)
        (DerivedCategory.Q.obj X.2.obj.obj) n :=
  RHom.injectiveDerivedHomLinearEquiv_self (R := R)
    X.1.unop.obj.obj X.2.obj.obj n

/-- Transport shifted Hom from standard derived images to the chosen K-injective localization. -/
@[stacks 0CS6 "explicit-base-ring Hom endpoint transport"]
noncomputable def modelEndpointEquiv
    (X : (Model (R := R) (C := C))ᵒᵖ × Model (R := R) (C := C)) (n : ℤ) :
    ShiftedHom (DerivedCategory.Q.obj X.1.unop.obj.obj)
        (DerivedCategory.Q.obj X.2.obj.obj) n ≃ₗ[R]
      ShiftedHom ((modelLocalization (R := R) (C := C)).obj X).1.unop
        ((modelLocalization (R := R) (C := C)).obj X).2 n :=
  (CategoryTheory.Linear.homCongr R
    (Over.derivedQObjIso (R := R) (A := C) X.1.unop.obj.obj)
    ((shiftFunctor _ n).mapIso
      (Over.derivedQObjIso (R := R) (A := C) X.2.obj.obj))).symm

/-- Reinsert the common universe lift on shifted Hom. -/
@[stacks 0CS6 "universe lift for explicit-base-ring shifted Hom"]
noncomputable def modelShiftedUp
    (X : (Model (R := R) (C := C))ᵒᵖ × Model (R := R) (C := C)) (n : ℤ) :
    ShiftedHom ((modelLocalization (R := R) (C := C)).obj X).1.unop
        ((modelLocalization (R := R) (C := C)).obj X).2 n ≃ₗ[R]
      (modelShifted (R := R) (C := C) n).obj X :=
  (ULift.moduleEquiv (R := R)
    (M := ShiftedHom ((modelLocalization (R := R) (C := C)).obj X).1.unop
      ((modelLocalization (R := R) (C := C)).obj X).2 n)).symm

/-- On K-injective pairs, derived-Hom cohomology is shifted Hom in the derived category. -/
@[stacks 0CS6 "K-injective explicit-base-ring Hom cohomology as shifted Hom"]
noncomputable def modelLinearEquiv
    (X : (Model (R := R) (C := C))ᵒᵖ × Model (R := R) (C := C)) (n : ℤ) :
    (modelCohomology (R := R) (C := C) n).obj X ≃ₗ[R]
      (modelShifted (R := R) (C := C) n).obj X :=
  (modelCohomologyDown (R := R) X n).trans <|
    (modelHomologyEquiv (R := R) X n).trans <|
      (modelExtEquiv (R := R) X n).trans <|
        (modelEndpointEquiv (R := R) X n).trans
          (modelShiftedUp (R := R) X n)

@[simp, stacks 0CS6 "pointwise explicit-base-ring K-injective cohomology representation"]
theorem modelLinearEquiv_apply
    (X : (Model (R := R) (C := C))ᵒᵖ × Model (R := R) (C := C)) (n : ℤ)
    (x : (modelCohomology (R := R) (C := C) n).obj X) :
    modelLinearEquiv (R := R) X n x =
      modelShiftedUp (R := R) X n
        (modelEndpointEquiv (R := R) X n
          (modelExtEquiv (R := R) X n
      (modelHomologyEquiv (R := R) X n
              (modelCohomologyDown (R := R) X n x)))) := rfl

section DerivedHomComparison

variable [RHom.Has (R := R) (C := C)]

/-- The derived-Hom unit identifies global explicit-base-ring cohomology with its
K-injective strict model. -/
@[stacks 0CS6 "explicit-base-ring K-injective cohomology comparison"]
noncomputable def modelCohomologyAppIso
    (X : (Model (R := R) (C := C))ᵒᵖ × Model (R := R) (C := C)) (n : ℤ) :
    (modelLocalization (R := R) (C := C) ⋙ uliftFunctor (R := R) (C := C) n).obj X ≅
      (modelCohomology (R := R) (C := C) n).obj X :=
  (ModuleCat.uliftFunctor.{max v w} R).mapIso
    ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) n).mapIso
      (RHom.unitAppIsoOfKInjective (R := R) (C := C)
        X.1.unop.obj.obj X.2.obj.obj).symm)

/-- Naturality of the explicit-base-ring K-injective cohomology comparison. -/
@[reassoc, stacks 0CS6 "naturality of explicit-base-ring K-injective cohomology comparison"]
theorem modelCohomologyAppIso_naturality (n : ℤ)
    {X Y : (Model (R := R) (C := C))ᵒᵖ × Model (R := R) (C := C)} (f : X ⟶ Y) :
    (modelLocalization (R := R) (C := C) ⋙ uliftFunctor (R := R) (C := C) n).map f ≫
        (modelCohomologyAppIso (R := R) (C := C) Y n).hom =
      (modelCohomologyAppIso (R := R) (C := C) X n).hom ≫
        (modelCohomology (R := R) (C := C) n).map f := by
  let eX := RHom.unitAppIsoOfKInjective (R := R) (C := C)
    X.1.unop.obj.obj X.2.obj.obj
  let eY := RHom.unitAppIsoOfKInjective (R := R) (C := C)
    Y.1.unop.obj.obj Y.2.obj.obj
  let g :
      (Opposite.op
          (⟨X.1.unop.obj.obj⟩ : DifferentialGradedCategory.K R (CochainComplex C ℤ)),
        (⟨X.2.obj.obj⟩ : DifferentialGradedCategory.K R (CochainComplex C ℤ))) ⟶
        (Opposite.op
          (⟨Y.1.unop.obj.obj⟩ : DifferentialGradedCategory.K R (CochainComplex C ℤ)),
        (⟨Y.2.obj.obj⟩ : DifferentialGradedCategory.K R (CochainComplex C ℤ))) :=
    (f.1.unop.hom.op, f.2.hom)
  have hunit :
      (RHom.localization (R := R) (C := C) ⋙ RHom.functor (R := R) (C := C)).map
          g ≫ eY.inv =
        eX.inv ≫ (RHom.source (R := R) (C := C)).map
          g := by
    rw [← cancel_mono eY.hom]
    rw [Category.assoc, eY.inv_hom_id, Category.comp_id, Category.assoc]
    change _ = eX.inv ≫
      ((RHom.source (R := R) (C := C)).map g ≫
        (RHom.unit (R := R) (C := C)).app _)
    rw [(RHom.unit (R := R) (C := C)).naturality g]
    change _ = eX.inv ≫ (eX.hom ≫ _)
    simp
  change
    (ModuleCat.uliftFunctor.{max v w} R).map
          ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) n).map
            ((RHom.localization (R := R) (C := C) ⋙ RHom.functor (R := R) (C := C)).map g)) ≫
        (ModuleCat.uliftFunctor.{max v w} R).map
          ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) n).map eY.inv) =
      (ModuleCat.uliftFunctor.{max v w} R).map
          ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) n).map eX.inv) ≫
        (ModuleCat.uliftFunctor.{max v w} R).map
          ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) n).map
            ((RHom.source (R := R) (C := C)).map g))
  simpa only [Functor.map_comp] using
    congrArg (fun k ↦
      (ModuleCat.uliftFunctor.{max v w} R).map
        ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) n).map k)) hunit

/-- Global explicit-base-ring cohomology restricted to K-injectives is its strict model. -/
@[stacks 0CS6 "explicit-base-ring K-injective cohomology model isomorphism"]
noncomputable def modelCohomologyIso (n : ℤ) :
    modelLocalization (R := R) (C := C) ⋙ uliftFunctor (R := R) (C := C) n ≅
      modelCohomology (R := R) (C := C) n :=
  NatIso.ofComponents (fun X => modelCohomologyAppIso (R := R) (C := C) X n)
    (fun {_ _} f => modelCohomologyAppIso_naturality (R := R) (C := C) n f)

end DerivedHomComparison

section ModelNaturality

/-- Associate the two functorial factors without unfolding category presentations. -/
private theorem map_comp_middle_assoc {D E : Type*} [Category D] [Category E]
    (T : D ⥤ E) {A B K : E} {X Y Z : D}
    (a : A ⟶ B) (b : B ⟶ K) (z : K ⟶ T.obj X)
    (d : X ⟶ Y) (e : Y ⟶ Z) :
    (a ≫ b) ≫ z ≫ T.map (d ≫ e) =
      a ≫ (b ≫ z ≫ T.map d) ≫ T.map e := by
  simp only [Functor.map_comp, Category.assoc]

/-- Naturality of the explicit-base-ring K-injective cohomology-to-shifted-Hom equivalence. -/
@[reassoc, stacks 0CS6 "naturality of explicit-base-ring shifted-Hom equivalence"]
theorem modelLinearEquiv_naturality (n : ℤ)
    {X Y : (Model (R := R) (C := C))ᵒᵖ × Model (R := R) (C := C)} (f : X ⟶ Y) :
    (modelCohomology (R := R) (C := C) n).map f ≫
        (modelLinearEquiv (R := R) Y n).toModuleIso.hom =
        (modelLinearEquiv (R := R) X n).toModuleIso.hom ≫
        (modelShifted (R := R) (C := C) n).map f := by
  obtain ⟨f₁, hf₁⟩ := @K.exists_rep R _ (CochainComplex C ℤ)
    (CochainComplex.differentialGradedCategory C R) _ _ f.1.unop.hom
  obtain ⟨f₂, hf₂⟩ := @K.exists_rep R _ (CochainComplex C ℤ)
    (CochainComplex.differentialGradedCategory C R) _ _ f.2.hom
  change CochainComplex.Enriched.Over.ClosedHom R Y.1.unop.obj.obj X.1.unop.obj.obj at f₁
  change CochainComplex.Enriched.Over.ClosedHom R X.2.obj.obj Y.2.obj.obj at f₂
  have hq₁ :
      (CochainComplex.Enriched.Over.toMathlib (R := R) (C := C)).map
          (@CompHom.toHomotopyClass R _ _
            (CochainComplex.differentialGradedCategory C R) _ _ f₁) =
        (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
          (CochainComplex.Enriched.Over.toHom (R := R) (C := C) f₁) := rfl
  have hq₂ :
      (CochainComplex.Enriched.Over.toMathlib (R := R) (C := C)).map
          (@CompHom.toHomotopyClass R _ _
            (CochainComplex.differentialGradedCategory C R) _ _ f₂) =
        (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
          (CochainComplex.Enriched.Over.toHom (R := R) (C := C) f₂) := rfl
  have hmap :
      @DifferentialGradedCategory.HomComplex.Derived.mapHomotopy R _
          (CochainComplex C ℤ) (CochainComplex.differentialGradedCategory C R)
          (ModuleCat.hasDerivedCategory R) _ _ _ _
          (@CompHom.toHomotopyClass R _ _
            (CochainComplex.differentialGradedCategory C R) _ _ f₁)
          (@CompHom.toHomotopyClass R _ _
            (CochainComplex.differentialGradedCategory C R) _ _ f₂) =
        DerivedCategory.Q.map (CochainComplex.Enriched.Over.homComplexMap (R := R)
          (CochainComplex.Enriched.Over.toHom (R := R) (C := C) f₁)
          (CochainComplex.Enriched.Over.toHom (R := R) (C := C) f₂)) := by
    erw [@DifferentialGradedCategory.HomComplex.Derived.mapHomotopy_mk R _
        (CochainComplex C ℤ) (CochainComplex.differentialGradedCategory C R)
        (ModuleCat.hasDerivedCategory R) _ _ _ _ f₁ f₂]
    congr 1
    ext i x
    simp [DifferentialGradedCategory.HomComplex.Derived.compMap,
      CochainComplex.Enriched.Over.homComplexMap,
      CochainComplex.HomComplex.map,
      DifferentialGradedCategory.HomComplex.precomp,
      DifferentialGradedCategory.HomComplex.postcomp,
      DifferentialGradedCategory.HomComplex.precompLinear,
      DifferentialGradedCategory.HomComplex.postcompLinear,
      CochainComplex.Enriched.Over.toHom,
      CochainComplex.HomComplex.closedHom]
  ext x
  change modelLinearEquiv (R := R) Y n
      ((modelCohomology (R := R) (C := C) n).map f x) =
    (modelShifted (R := R) (C := C) n).map f
      (modelLinearEquiv (R := R) X n x)
  rw [modelLinearEquiv_apply, modelLinearEquiv_apply]
  have hcoh :
      modelHomologyEquiv (R := R) Y n
          (modelCohomologyDown (R := R) Y n
            ((modelCohomology (R := R) (C := C) n).map f x)) =
        HomologicalComplex.homologyMap
          (CochainComplex.Enriched.Over.homComplexMap (R := R)
            (CochainComplex.Enriched.Over.toHom (R := R) (C := C) f₁)
            (CochainComplex.Enriched.Over.toHom (R := R) (C := C) f₂)) n
          (modelHomologyEquiv (R := R) X n
            (modelCohomologyDown (R := R) X n x)) := by
    simp [modelCohomologyDown, modelHomologyEquiv]
    rw [hf₁, hf₂]
    simp only [RHom.source, DifferentialGradedCategory.HomComplex.Derived.functor]
    erw [hmap]
    let k := CochainComplex.Enriched.Over.homComplexMap (R := R)
      (CochainComplex.Enriched.Over.toHom (R := R) (C := C) f₁)
      (CochainComplex.Enriched.Over.toHom (R := R) (C := C) f₂)
    change
      (ConcreteCategory.hom
          ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) n).map
              (DerivedCategory.Q.map k) ≫
            (DerivedCategory.homologyFunctorFactors (ModuleCat.{v} R) n).hom.app _))
          (ULift.moduleEquiv (R := R) x) =
        (ConcreteCategory.hom
          ((DerivedCategory.homologyFunctorFactors (ModuleCat.{v} R) n).hom.app _ ≫
            HomologicalComplex.homologyMap k n))
          (ULift.moduleEquiv (R := R) x)
    exact ConcreteCategory.congr_hom
      (DerivedCategory.homologyFunctorFactors_hom_naturality k n)
      (ULift.moduleEquiv (R := R) x)
  rw [hcoh]
  simp only [modelExtEquiv,
    RHom.injectiveDerivedHomLinearEquiv_self,
    RHom.injectiveDerivedHomLinearEquiv_apply,
    RHom.injectiveDerivedHomLinearMap_apply,
    RHom.injectiveDerivedHomOfHomology]
  rw [RHom.derivedHomOfHomology_naturality]
  simp only [Functor.map_id, asIso_inv, IsIso.inv_id, Category.comp_id]
  let z := RHom.derivedHomOfHomology (R := R) X.1.unop.obj.obj X.2.obj.obj n
    (modelHomologyEquiv (R := R) X n
      (modelCohomologyDown (R := R) X n x))
  have hsource :
      (CochainComplex.Enriched.Over.derivedQ (R := R) (A := C)).map
          (@CompHom.toHomotopyClass R _ _
            (CochainComplex.differentialGradedCategory C R) _ _ f₁) ≫
        (CochainComplex.Enriched.Over.derivedQObjIso (R := R) (A := C)
          X.1.unop.obj.obj).hom =
      (CochainComplex.Enriched.Over.derivedQObjIso (R := R) (A := C)
          Y.1.unop.obj.obj).hom ≫
        DerivedCategory.Q.map
          (CochainComplex.Enriched.Over.toHom (R := R) (C := C) f₁) := by
    change DerivedCategory.Qh.map
        ((CochainComplex.Enriched.Over.toMathlib (R := R) (C := C)).map
          (@CompHom.toHomotopyClass R _ _
            (CochainComplex.differentialGradedCategory C R) _ _ f₁)) ≫
          (DerivedCategory.quotientCompQhIso C).hom.app _ =
      (DerivedCategory.quotientCompQhIso C).hom.app _ ≫
        DerivedCategory.Q.map
          (CochainComplex.Enriched.Over.toHom (R := R) (C := C) f₁)
    rw [hq₁]
    exact DerivedCategory.quotientCompQhIso_hom_naturality _
  have htarget :
      DerivedCategory.Q.map
          (CochainComplex.Enriched.Over.toHom (R := R) (C := C) f₂) ≫
        (CochainComplex.Enriched.Over.derivedQObjIso (R := R) (A := C)
          Y.2.obj.obj).inv =
      (CochainComplex.Enriched.Over.derivedQObjIso (R := R) (A := C)
          X.2.obj.obj).inv ≫
        (CochainComplex.Enriched.Over.derivedQ (R := R) (A := C)).map
          (@CompHom.toHomotopyClass R _ _
            (CochainComplex.differentialGradedCategory C R) _ _ f₂) := by
    change DerivedCategory.Q.map
          (CochainComplex.Enriched.Over.toHom (R := R) (C := C) f₂) ≫
        (DerivedCategory.quotientCompQhIso C).inv.app _ =
      (DerivedCategory.quotientCompQhIso C).inv.app _ ≫
        DerivedCategory.Qh.map
          ((CochainComplex.Enriched.Over.toMathlib (R := R) (C := C)).map
            (@CompHom.toHomotopyClass R _ _
              (CochainComplex.differentialGradedCategory C R) _ _ f₂))
    rw [hq₂]
    exact DerivedCategory.quotientCompQhIso_inv_naturality _
  have htargetShift := congrArg (fun k ↦ (shiftFunctor (DerivedCategory C) n).map k) htarget
  simp only [Functor.map_comp] at htargetShift
  have hq₁Q :
      (CochainComplex.Enriched.Over.derivedQ (R := R) (A := C)).map
          (@CompHom.toHomotopyClass R _ _
            (CochainComplex.differentialGradedCategory C R) _ _ f₁) =
        DerivedCategory.Qh.map
          ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
            (CochainComplex.Enriched.Over.toHom (R := R) (C := C) f₁)) := by
    exact congrArg (fun k ↦ DerivedCategory.Qh.map k) hq₁
  have hq₂Q :
      (CochainComplex.Enriched.Over.derivedQ (R := R) (A := C)).map
          (@CompHom.toHomotopyClass R _ _
            (CochainComplex.differentialGradedCategory C R) _ _ f₂) =
        DerivedCategory.Qh.map
          ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
            (CochainComplex.Enriched.Over.toHom (R := R) (C := C) f₂)) := by
    exact congrArg (fun k ↦ DerivedCategory.Qh.map k) hq₂
  have hendpoint :
      modelEndpointEquiv (R := R) Y n
          (DerivedCategory.Q.map
              (CochainComplex.Enriched.Over.toHom (R := R) (C := C) f₁) ≫
            z ≫ (shiftFunctor (DerivedCategory C) n).map
              (DerivedCategory.Q.map
                (CochainComplex.Enriched.Over.toHom (R := R) (C := C) f₂))) =
        DerivedCategory.Qh.map
            ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
              (CochainComplex.Enriched.Over.toHom (R := R) (C := C) f₁)) ≫
          modelEndpointEquiv (R := R) X n z ≫
            (shiftFunctor (DerivedCategory C) n).map
              (DerivedCategory.Qh.map
                ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
                  (CochainComplex.Enriched.Over.toHom (R := R) (C := C) f₂))) := by
    change
      (CategoryTheory.Linear.homCongr R
        (CochainComplex.Enriched.Over.derivedQObjIso (R := R) (A := C)
          Y.1.unop.obj.obj)
        ((shiftFunctor (DerivedCategory C) n).mapIso
          (CochainComplex.Enriched.Over.derivedQObjIso (R := R) (A := C)
            Y.2.obj.obj))).symm
          (DerivedCategory.Q.map
              (CochainComplex.Enriched.Over.toHom (R := R) (C := C) f₁) ≫
            z ≫ (shiftFunctor (DerivedCategory C) n).map
              (DerivedCategory.Q.map
                (CochainComplex.Enriched.Over.toHom (R := R) (C := C) f₂))) =
        DerivedCategory.Qh.map
            ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
              (CochainComplex.Enriched.Over.toHom (R := R) (C := C) f₁)) ≫
          (CategoryTheory.Linear.homCongr R
            (CochainComplex.Enriched.Over.derivedQObjIso (R := R) (A := C)
              X.1.unop.obj.obj)
            ((shiftFunctor (DerivedCategory C) n).mapIso
              (CochainComplex.Enriched.Over.derivedQObjIso (R := R) (A := C)
                X.2.obj.obj))).symm z ≫
            (shiftFunctor (DerivedCategory C) n).map
              (DerivedCategory.Qh.map
                ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
                  (CochainComplex.Enriched.Over.toHom (R := R) (C := C) f₂)))
    rw [Linear.homCongr_symm_apply, Linear.homCongr_symm_apply]
    simp only [← Category.assoc]
    rw [← hsource]
    simp only [Category.assoc]
    erw [htargetShift]
    simp only [Functor.mapIso_inv]
    erw [hq₁Q, hq₂Q]
    exact map_comp_middle_assoc (shiftFunctor (DerivedCategory C) n)
      (DerivedCategory.Qh.map
        ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
          (CochainComplex.Enriched.Over.toHom (R := R) (C := C) f₁)))
      (CochainComplex.Enriched.Over.derivedQObjIso
        (R := R) (A := C) X.1.unop.obj.obj).hom z
      (CochainComplex.Enriched.Over.derivedQObjIso
        (R := R) (A := C) X.2.obj.obj).inv
      (DerivedCategory.Qh.map
        ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
          (CochainComplex.Enriched.Over.toHom (R := R) (C := C) f₂)))
  rw [hendpoint]
  simp [modelShiftedUp, modelShifted, shiftedFunctor, modelLocalization,
    hf₁, hf₂, hq₁, hq₂, Functor.uncurry_obj_map,
    ModuleCat.uliftFunctor_map, ShiftedHom.linearCoyoneda_map]
  change ULift.up _ = ULift.up _
  congr 1
  let q₁ := DerivedCategory.Qh.map
    ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
      (CochainComplex.Enriched.Over.toHom (R := R) (C := C) f₁))
  let q₂ := DerivedCategory.Qh.map
    ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
      (CochainComplex.Enriched.Over.toHom (R := R) (C := C) f₂))
  let a := (ShiftedHom.targetMap R q₁.op.unop n).app
    ((modelLocalization (R := R) (C := C)).obj X).2
  let b := ((ShiftedHom.linearCoyoneda R (DerivedCategory C) n).obj
    ((modelLocalization (R := R) (C := C)).obj Y).1).map q₂
  change q₁ ≫ modelEndpointEquiv (R := R) X n z ≫
      (shiftFunctor (DerivedCategory C) n).map q₂ =
    ModuleCat.Hom.hom (a ≫ b) (modelEndpointEquiv (R := R) X n z)
  rw [ModuleCat.comp_apply]
  dsimp only [a, b]
  rw [ShiftedHom.targetMap_app_apply]
  change q₁ ≫ modelEndpointEquiv (R := R) X n z ≫
      (shiftFunctor (DerivedCategory C) n).map q₂ =
    (q₁.op.unop ≫ modelEndpointEquiv (R := R) X n z) ≫
      (shiftFunctor (DerivedCategory C) n).map q₂
  simp only [Quiver.Hom.unop_op, Category.assoc]

end ModelNaturality

/-- Strict explicit-base-ring Hom cohomology is naturally shifted Hom on the model category. -/
@[stacks 0CS6 "explicit-base-ring K-injective cohomology representation"]
noncomputable def modelIso (n : ℤ) :
    modelCohomology (R := R) (C := C) n ≅
      modelShifted (R := R) (C := C) n :=
  NatIso.ofComponents (fun X => (modelLinearEquiv (R := R) X n).toModuleIso)
    (fun {_ _} f => modelLinearEquiv_naturality (R := R) (C := C) n f)

section DerivedHomComparison

variable [RHom.Has (R := R) (C := C)]

/-- The K-injective restriction of global explicit-base-ring cohomology is shifted Hom. -/
@[stacks 0CS6 "explicit-base-ring K-injective cohomology comparison isomorphism"]
noncomputable def modelComparisonIso (n : ℤ) :
    modelLocalization (R := R) (C := C) ⋙ uliftFunctor (R := R) (C := C) n ≅
      modelLocalization (R := R) (C := C) ⋙ shiftedFunctor (R := R) (C := C) n :=
  modelCohomologyIso (R := R) (C := C) n ≪≫ modelIso (R := R) (C := C) n

end DerivedHomComparison

section Grothendieck

variable [IsGrothendieckAbelian.{g} C]

-- Local instance justification (defeq pin): use the existing total-derived Hom witness for this exact R-linear category.
local instance : RHom.Has (R := R) (C := C) :=
  RHom.hasRightDerivedFunctor (R := R) (C := C)

/-- Degreewise explicit-base-ring derived Hom cohomology is represented by shifted Hom. -/
@[stacks 0CS6 "explicit-base-ring derived Hom cohomology representation"]
noncomputable def iso (n : ℤ) :
    uliftFunctor (R := R) (C := C) n ≅ shiftedFunctor (R := R) (C := C) n :=
  Localization.liftNatIso (modelLocalization (R := R) (C := C))
    (modelQis (R := R) (C := C))
    (modelLocalization (R := R) (C := C) ⋙ uliftFunctor (R := R) (C := C) n)
    (modelLocalization (R := R) (C := C) ⋙ shiftedFunctor (R := R) (C := C) n)
    (uliftFunctor (R := R) (C := C) n)
    (shiftedFunctor (R := R) (C := C) n)
    (modelComparisonIso (R := R) (C := C) n)

/-- The unlifted explicit-base-ring cohomology-to-shifted-Hom linear equivalence. -/
@[stacks 0CS6 "explicit-base-ring derived Hom cohomology as shifted Hom"]
noncomputable def linearEquiv (M N : DerivedCategory.{w} C) (n : ℤ) :
    (functor (R := R) (C := C) n).obj (Opposite.op M, N) ≃ₗ[R]
      ShiftedHom M N n :=
  (ULift.moduleEquiv (R := R)
      (M := (functor (R := R) (C := C) n).obj (Opposite.op M, N))).symm.trans <|
    ((iso (R := R) (C := C) n).app (Opposite.op M, N)).toLinearEquiv.trans <|
      ULift.moduleEquiv (R := R) (M := ShiftedHom M N n)

/-- Pointwise evaluation of the explicit-base-ring cohomology representation. -/
@[simp, stacks 0CS6 "pointwise explicit-base-ring derived Hom cohomology representation"]
theorem linearEquiv_apply (M N : DerivedCategory.{w} C) (n : ℤ)
    (x : (functor (R := R) (C := C) n).obj (Opposite.op M, N)) :
    linearEquiv (R := R) (C := C) M N n x =
      ((iso (R := R) (C := C) n).hom.app (Opposite.op M, N) (ULift.up x)).down := rfl

/-- Naturality of the lifted explicit-base-ring cohomology representation. -/
@[reassoc, stacks 0CS6 "naturality of explicit-base-ring derived Hom cohomology representation"]
theorem iso_naturality (n : ℤ)
    {X Y : (DerivedCategory.{w} C)ᵒᵖ × DerivedCategory.{w} C} (f : X ⟶ Y) :
    (uliftFunctor (R := R) (C := C) n).map f ≫
        (iso (R := R) (C := C) n).hom.app Y =
      (iso (R := R) (C := C) n).hom.app X ≫
        (shiftedFunctor (R := R) (C := C) n).map f :=
  (iso (R := R) (C := C) n).hom.naturality f

end Grothendieck

end CategoryTheory.CochainComplex.Enriched.Over.RHom.Cohomology
