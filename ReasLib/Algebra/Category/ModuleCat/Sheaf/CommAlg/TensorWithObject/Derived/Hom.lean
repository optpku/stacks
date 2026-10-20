/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.CommAlg.TensorWithObject.Derived.Functor
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Derived.RHom
public import ReasLib.Algebra.Homology.DifferentialGradedModule.PropertyP.Localization
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Enriched
public import ReasLib.Algebra.Category.DifferentialGraded.Functor.HomComplex.DerivedMap

/-!
# Derived tensor-Hom comparison over an algebra sheaf

This file is the arbitrary-coefficient-ring form of the tensor-Hom comparison.  The source is
derived Hom of right DG modules over `endDGA K`; the target applies derived tensoring with `K` in
both variables and then takes the derived enriched Hom of `O`-module sheaves.  The comparison is
descended from property-(P) representatives, so the public morphism is independent of any chosen
resolution.
-/

@[expose] public section

noncomputable section

universe r u v w z

open CategoryTheory
open DifferentialGradedCategory
open scoped DifferentialGradedCategory SheafOfModules.CommAlg

namespace SheafOfModules.CommAlg.TensorWithObject.Derived.Hom

variable {R : Type r} [CommRing R]
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ (CommAlgCat.{w} R) CommRingCat.{w})]
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [UnivLE.{max u v, max u z}]
variable [HasWeakSheafify J AddCommGrpCat.{max u z}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u z}]
variable {O : Sheaf J (CommAlgCat.{w} R)}

/-- The paired derived DG-module category on which tensor-Hom comparison functors act. -/
@[stacks 0CS6 "domain of the arbitrary-ring tensor-Hom comparison"]
abbrev Domain (K : Complex.{r, u, v, w, max u z} O) :=
  (DifferentialGradedModule.Derived.Category.{r, max u z} (endDGA K))ᵒᵖ ×
    DifferentialGradedModule.Derived.Category.{r, max u z} (endDGA K)

namespace Source

/-- Derived `RHom` of right DG modules over the endomorphism DGA of `K`. -/
@[stacks 0CS6 "source of the arbitrary-ring tensor-Hom comparison"]
noncomputable abbrev functor (K : Complex.{r, u, v, w, max u z} O) :
    Domain K ⥤ D((ModuleCat R)) :=
  DifferentialGradedModule.Derived.RHom.functor (endDGA K)

end Source

namespace Target

variable [SheafOfModules.CommAlg.Derived.RHom.Has.{r, u, v, w, max u z} O]

/-- Derived tensoring with `K` in both variables followed by sheaf-module derived `RHom`. -/
@[stacks 0CS6 "target of the arbitrary-ring tensor-Hom comparison"]
noncomputable abbrev functor (K : Complex.{r, u, v, w, max u z} O) :
    Domain K ⥤ D((ModuleCat R)) :=
  ((SheafOfModules.CommAlg.TensorWithObject.Derived.tensorFunctor K).op.prod
      (SheafOfModules.CommAlg.TensorWithObject.Derived.tensorFunctor K)) ⋙
    SheafOfModules.CommAlg.Derived.RHom.functor.{r, u, v, w, max u z} O

end Target

namespace PropertyP

/-- Pairs of property-(P) DG homotopy models used to construct the comparison. -/
@[stacks 0CS6 "property-P domain of the arbitrary-ring tensor-Hom comparison"]
abbrev Domain (K : Complex.{r, u, v, w, max u z} O) :=
  (DifferentialGradedModule.Homotopy.propertyP (endDGA K)).FullSubcategoryᵒᵖ ×
    (DifferentialGradedModule.Homotopy.propertyP (endDGA K)).FullSubcategory

/-- The simultaneous quasi-isomorphism system on property-(P) pairs. -/
@[stacks 0CS6 "property-P denominators for the arbitrary-ring comparison"]
abbrev qis (K : Complex.{r, u, v, w, max u z} O) : MorphismProperty (Domain K) :=
  (DifferentialGradedModule.Homotopy.PropertyP.qis (endDGA K)).op.prod
    (DifferentialGradedModule.Homotopy.PropertyP.qis (endDGA K))

/-- The localization from property-(P) homotopy models to arbitrary derived DG modules. -/
@[stacks 0CS6 "property-P localization for the arbitrary-ring comparison"]
noncomputable abbrev localization (K : Complex.{r, u, v, w, max u z} O) :=
  (DifferentialGradedModule.Homotopy.PropertyP.localization (endDGA K)).op.prod
    (DifferentialGradedModule.Homotopy.PropertyP.localization (endDGA K))

section WithTargetRHom

variable [SheafOfModules.CommAlg.Derived.RHom.Has.{r, u, v, w, max u z} O]

/-- The strict comparison component on a pair of property-(P) modules. -/
@[stacks 0CS6 "property-P component of the arbitrary-ring tensor-Hom comparison"]
noncomputable def comparisonApp (K : Complex.{r, u, v, w, max u z} O)
    (M N : TensorWithObject.Modules K)
    (hM : DifferentialGradedModule.HasPropertyP (endDGA K) M)
    (hN : DifferentialGradedModule.HasPropertyP (endDGA K) N) :
    (Source.functor K).obj
        (Opposite.op ((DifferentialGradedModule.Derived.fromModules
          (endDGA K)).obj M),
          (DifferentialGradedModule.Derived.fromModules (endDGA K)).obj N) ⟶
      (Target.functor K).obj
        (Opposite.op ((DifferentialGradedModule.Derived.fromModules
          (endDGA K)).obj M),
          (DifferentialGradedModule.Derived.fromModules (endDGA K)).obj N) :=
  (DifferentialGradedModule.Derived.RHom.unitAppIsoOfPropertyP
      (endDGA K) M N hM).inv ≫
    (DifferentialGradedCategory.HomComplex.Derived.mapNatTrans
      (TensorWithObject.tensorFunctor K)).app
        (Opposite.op
            ((DifferentialGradedModule.toK (endDGA K)).obj M),
          ((DifferentialGradedModule.toK (endDGA K)).obj N)) ≫
    SheafOfModules.CommAlg.Derived.RHom.unitApp.{r, u, v, w, max u z} O
      ((TensorWithObject.tensorFunctor K).obj M)
      ((TensorWithObject.tensorFunctor K).obj N) ≫
    (SheafOfModules.CommAlg.Derived.RHom.functor.{r, u, v, w, max u z} O).map
        ((SheafOfModules.CommAlg.TensorWithObject.Derived.tensorCounitAppIso K M hM).hom.op,
          (SheafOfModules.CommAlg.TensorWithObject.Derived.tensorCounitAppIso K N hN).inv)

/-- The component indexed by a pair of property-(P) full-subcategory objects. -/
@[stacks 0CS6 "property-P comparison component over an algebra sheaf"]
noncomputable abbrev component (K : Complex.{r, u, v, w, max u z} O) (X : Domain K) :=
  comparisonApp K X.1.unop.obj.obj X.2.obj.obj X.1.unop.property X.2.property

/-- Naturality of the strict property-(P) comparison. -/
@[reassoc, stacks 0CS6 "naturality of the property-P arbitrary-ring comparison"]
theorem comparison_naturality (K : Complex.{r, u, v, w, max u z} O)
    {X Y : Domain K} (f : X ⟶ Y) :
    (localization K ⋙ Source.functor K).map f ≫ component K Y =
      component K X ≫ (localization K ⋙ Target.functor K).map f := sorry

/-- The property-(P) components form the natural transformation before descent. -/
@[stacks 0CS6 "property-P arbitrary-ring tensor-Hom comparison"]
noncomputable def comparison (K : Complex.{r, u, v, w, max u z} O) :
    localization K ⋙ Source.functor K ⟶ localization K ⋙ Target.functor K where
  app X := component K X
  naturality _ _ f := comparison_naturality K f

end WithTargetRHom

end PropertyP

section WithTargetRHom

variable [SheafOfModules.CommAlg.Derived.RHom.Has.{r, u, v, w, max u z} O]

-- The localization lift needs a larger elaboration budget in this universe-polymorphic owner;
-- the option is local to construction and does not occur in the public declaration type.
set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 80000 in
/-- Lemma 22.35.4 (0CS6): the canonical derived tensor-Hom comparison over the sheaf of
`R`-algebras `O`. -/
@[stacks 0CS6 "arbitrary-ring derived tensor-Hom comparison"]
noncomputable def comparison (K : Complex.{r, u, v, w, max u z} O) :
    Source.functor K ⟶ Target.functor K :=
  Localization.liftNatTrans (PropertyP.localization K) (PropertyP.qis K)
    (PropertyP.localization K ⋙ Source.functor K)
    (PropertyP.localization K ⋙ Target.functor K)
    (Source.functor K) (Target.functor K) (PropertyP.comparison K)

/-- Restricting the descended comparison to property-(P) models recovers its strict component. -/
@[reassoc, stacks 0CS6 "property-P restriction of the arbitrary-ring comparison"]
theorem comparison_fac (K : Complex.{r, u, v, w, max u z} O) :
    Functor.whiskerLeft (PropertyP.localization K) (comparison K) =
      PropertyP.comparison K := sorry

/-- The component of the arbitrary-ring comparison at any derived DG-module pair. -/
@[stacks 0CS6 "objectwise arbitrary-ring derived tensor-Hom comparison"]
noncomputable abbrev comparisonApp (K : Complex.{r, u, v, w, max u z} O)
    (M N : DifferentialGradedModule.Derived.Category (endDGA K)) :
    (Source.functor K).obj (Opposite.op M, N) ⟶
      (Target.functor K).obj (Opposite.op M, N) :=
  (comparison K).app (Opposite.op M, N)

/-- On property-(P) representatives, the descended map is the strict enriched-Hom construction. -/
@[stacks 0CS6 "property-P computation of the arbitrary-ring comparison"]
theorem comparison_app_propertyP (K : Complex.{r, u, v, w, max u z} O)
    (M N : TensorWithObject.Modules K)
    (hM : DifferentialGradedModule.HasPropertyP (endDGA K) M)
    (hN : DifferentialGradedModule.HasPropertyP (endDGA K) N) :
      comparisonApp K
        ((DifferentialGradedModule.Derived.fromModules (endDGA K)).obj M)
        ((DifferentialGradedModule.Derived.fromModules (endDGA K)).obj N) =
      PropertyP.comparisonApp K M N hM hN := sorry

end WithTargetRHom

section InstanceChecks

variable (K : Complex.{r, u, v, w, max u z} O)

#synth (PropertyP.localization K).IsLocalization (PropertyP.qis K)
#synth Localization.Lifting (PropertyP.localization K) (PropertyP.qis K)
  (PropertyP.localization K ⋙ Source.functor K) (Source.functor K)

end InstanceChecks

section TargetInstanceChecks

variable [SheafOfModules.CommAlg.Derived.RHom.Has.{r, u, v, w, max u z} O]
variable (K : Complex.{r, u, v, w, max u z} O)

#synth Localization.Lifting (PropertyP.localization K) (PropertyP.qis K)
  (PropertyP.localization K ⋙ Target.functor K) (Target.functor K)

end TargetInstanceChecks

end SheafOfModules.CommAlg.TensorWithObject.Derived.Hom
