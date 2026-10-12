/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import ReasLib.Algebra.Category.DifferentialGraded.Functor.HomComplex.Derived
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Derived
public import ReasLib.Algebra.Homology.DifferentialGradedModule.PropertyI.KInjective
public import ReasLib.Algebra.Homology.DifferentialGradedModule.PropertyI.Resolution
public import ReasLib.Algebra.Homology.DifferentialGradedModule.PropertyP
public import ReasLib.CategoryTheory.Functor.Derived.ComputesAt.Total
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived Hom for Differential Graded Modules

This leaf owns the simultaneous total right-derived enriched Hom bifunctor for right modules
over an arbitrary cochain DG algebra.  Its existence instance is attached to the DG algebra,
so downstream users do not pass a separate derivability witness.
-/

@[expose] public section

noncomputable section

open CategoryTheory DifferentialGradedCategory
open scoped DifferentialGradedCategory

universe u v

namespace DifferentialGradedModule.Derived.RHom

variable {R : Type u} [CommRing R]

/-- The homotopy-level enriched Hom bifunctor for right DG `A`-modules. -/
@[stacks 0CS6 "homotopy-level DG-module Hom bifunctor"]
noncomputable abbrev source (A : CochainDGAlgebra.{u, v} R) :=
  (DifferentialGradedCategory.HomComplex.Derived.functor
    (R := R) (A := DifferentialGradedModule.{u, v} A) :
      (K R (DifferentialGradedModule.{u, v} A))ᵒᵖ ×
          K R (DifferentialGradedModule.{u, v} A) ⥤
        DerivedCategory (ModuleCat.{v} R))

/-- The simultaneous quasi-isomorphism system for the two variables of derived Hom. -/
@[stacks 0CS6 "product quasi-isomorphism property for DG-module derived Hom"]
abbrev qis (A : CochainDGAlgebra.{u, v} R) :=
  DifferentialGradedCategory.HomComplex.Derived.qis
    (DifferentialGradedModule.quasiIso A)

/-- The product localization from pairs of DG homotopy objects to pairs of derived objects. -/
@[stacks 0CS6 "product localization for DG-module derived Hom"]
noncomputable abbrev localization (A : CochainDGAlgebra.{u, v} R) :=
  DifferentialGradedCategory.HomComplex.Derived.localization
    (DifferentialGradedModule.Derived.Q A)

/-- The existence condition for simultaneous derived Hom of right DG `A`-modules. -/
@[stacks 0CS6 "existence condition for derived Hom of DG modules"]
abbrev Has (A : CochainDGAlgebra.{u, v} R) : Prop :=
  (source A).HasRightDerivedFunctor (qis A)

/-- A K-injective covariant entry computes simultaneous derived Hom, independently of the
contravariant entry. -/
@[stacks 070Y "K-injective computation of DG derived Hom"]
theorem computesAt_of_kInjective (A : CochainDGAlgebra.{u, v} R)
    (M I : DifferentialGradedModule.{u, v} A)
    (hI : DifferentialGradedModule.Homotopy.kInjective A
      ((DifferentialGradedModule.toK A).obj I)) :
    Functor.RightDerived.ComputesAt (source A) (qis A)
      (Opposite.op ((DifferentialGradedModule.toK A).obj M),
        (DifferentialGradedModule.toK A).obj I) := sorry

/-- A property-(I) covariant entry computes simultaneous derived Hom. -/
@[stacks 070Y "property-I computation of DG derived Hom"]
theorem computesAt_of_propertyI (A : CochainDGAlgebra.{u, v} R)
    (M I : DifferentialGradedModule.{u, v} A)
    (hI : DifferentialGradedModule.HasPropertyI A I) :
    Functor.RightDerived.ComputesAt (source A) (qis A)
      (Opposite.op ((DifferentialGradedModule.toK A).obj M),
        (DifferentialGradedModule.toK A).obj I) := sorry

/-- Property-(I) resolutions in the covariant variable suffice for simultaneous derived Hom to
exist; the contravariant variable needs no chosen resolution. -/
@[stacks 0CS6 "derived Hom from property-I resolutions"]
theorem ofResolutions (A : CochainDGAlgebra.{u, v} R)
    (hI : ∀ M : DifferentialGradedModule.{u, v} A,
      Nonempty (DifferentialGradedModule.PropertyI.Resolution A M)) :
    Has A := sorry

/-- Enriched Hom of right DG modules admits its simultaneous total right-derived functor. -/
@[stacks 0CS6 "existence of derived Hom for DG modules"]
instance hasRightDerivedFunctor (A : CochainDGAlgebra.{u, v} R) :
    (source A).HasRightDerivedFunctor (qis A) := sorry

/-- The `D(R)`-valued derived Hom bifunctor of right DG modules over `A`. -/
@[stacks 0CS6 "derived Hom bifunctor for DG modules"]
noncomputable def functor (A : CochainDGAlgebra.{u, v} R) :=
  (DifferentialGradedCategory.HomComplex.Derived.RHom.functor
    (DifferentialGradedModule.Derived.Q A)
    (DifferentialGradedModule.quasiIso A) :
      (DifferentialGradedModule.Derived.Category.{u, v} A)ᵒᵖ ×
          DifferentialGradedModule.Derived.Category.{u, v} A ⥤
        DerivedCategory (ModuleCat.{v} R))

/-- The curried DG-module `RHom` functor, with the source variable first. -/
@[stacks 0CS6 "curried DG-module derived Hom"]
noncomputable def curried (A : CochainDGAlgebra.{u, v} R) :=
  DifferentialGradedCategory.HomComplex.Derived.RHom.curried
    (DifferentialGradedModule.Derived.Q A)
    (DifferentialGradedModule.quasiIso A)

/-- The DG-module `RHom` functor with fixed target and varying source. -/
@[stacks 0CS6 "source-variable DG-module derived Hom"]
noncomputable def sourceFunctor (A : CochainDGAlgebra.{u, v} R)
    (N : DifferentialGradedModule.Derived.Category.{u, v} A) :=
  DifferentialGradedCategory.HomComplex.Derived.RHom.sourceFunctor
    (DifferentialGradedModule.Derived.Q A)
    (DifferentialGradedModule.quasiIso A) N

/-- The DG-module `RHom` functor with fixed source and varying target. -/
@[stacks 0CS6 "target-variable DG-module derived Hom"]
noncomputable def targetFunctor (A : CochainDGAlgebra.{u, v} R)
    (M : (DifferentialGradedModule.Derived.Category.{u, v} A)ᵒᵖ) :=
  DifferentialGradedCategory.HomComplex.Derived.RHom.targetFunctor
    (DifferentialGradedModule.Derived.Q A)
    (DifferentialGradedModule.quasiIso A) M

/-- The module-level source-variable derived Hom functor is additive. -/
@[stacks 0CS6 "additivity in the source variable of module derived Hom"]
noncomputable instance sourceFunctorAdditive
    (A : CochainDGAlgebra.{u, v} R)
    (N : DifferentialGradedModule.Derived.Category.{u, v} A) :
    (sourceFunctor A N).Additive := sorry

/-- The module-level source-variable derived Hom functor is `R`-linear. -/
@[stacks 0CS6 "linearity in the source variable of module derived Hom"]
noncomputable instance sourceFunctorLinear
    (A : CochainDGAlgebra.{u, v} R)
    (N : DifferentialGradedModule.Derived.Category.{u, v} A) :
    Functor.Linear R (sourceFunctor A N) := sorry

/-- The module-level target-variable derived Hom functor is additive. -/
@[stacks 0CS6 "additivity in the target variable of module derived Hom"]
noncomputable instance targetFunctorAdditive
    (A : CochainDGAlgebra.{u, v} R)
    (M : (DifferentialGradedModule.Derived.Category.{u, v} A)ᵒᵖ) :
    (targetFunctor A M).Additive := sorry

/-- The module-level target-variable derived Hom functor is `R`-linear. -/
@[stacks 0CS6 "linearity in the target variable of module derived Hom"]
noncomputable instance targetFunctorLinear
    (A : CochainDGAlgebra.{u, v} R)
    (M : (DifferentialGradedModule.Derived.Category.{u, v} A)ᵒᵖ) :
    Functor.Linear R (targetFunctor A M) := sorry

/-- The module-level fixed-target derived Hom functor has the expected object formula. -/
@[simp, stacks 0CS6 "source-variable module derived Hom object formula"]
theorem sourceFunctor_obj (A : CochainDGAlgebra.{u, v} R)
    (N : DifferentialGradedModule.Derived.Category.{u, v} A)
    (M : (DifferentialGradedModule.Derived.Category.{u, v} A)ᵒᵖ) :
    (sourceFunctor A N).obj M = (functor A).obj (M, N) := sorry

/-- The module-level fixed-source derived Hom functor has the expected object formula. -/
@[simp, stacks 0CS6 "target-variable module derived Hom object formula"]
theorem targetFunctor_obj (A : CochainDGAlgebra.{u, v} R)
    (M : (DifferentialGradedModule.Derived.Category.{u, v} A)ᵒᵖ)
    (N : DifferentialGradedModule.Derived.Category.{u, v} A) :
    (targetFunctor A M).obj N = (functor A).obj (M, N) := sorry

/-- Source maps of module-level derived Hom are the first components of product maps. -/
@[simp, stacks 0CS6 "source-variable module derived Hom map formula"]
theorem sourceFunctor_map (A : CochainDGAlgebra.{u, v} R)
    (N : DifferentialGradedModule.Derived.Category.{u, v} A)
    {M M' : (DifferentialGradedModule.Derived.Category.{u, v} A)ᵒᵖ}
    (f : M ⟶ M') :
    (sourceFunctor A N).map f = (functor A).map (f, 𝟙 N) := sorry

/-- Target maps of module-level derived Hom are the second components of product maps. -/
@[simp, stacks 0CS6 "target-variable module derived Hom map formula"]
theorem targetFunctor_map (A : CochainDGAlgebra.{u, v} R)
    (M : (DifferentialGradedModule.Derived.Category.{u, v} A)ᵒᵖ)
    {N N' : DifferentialGradedModule.Derived.Category.{u, v} A}
    (g : N ⟶ N') :
    (targetFunctor A M).map g = (functor A).map (𝟙 M, g) := sorry

/-- The universal map from enriched Hom on homotopy objects to derived Hom over `A`. -/
@[stacks 0CS6 "DG Hom to derived Hom"]
noncomputable abbrev unit (A : CochainDGAlgebra.{u, v} R) :=
  DifferentialGradedCategory.HomComplex.Derived.RHom.unit
    (DifferentialGradedModule.Derived.Q A)
    (DifferentialGradedModule.quasiIso A)

/-- The derived-Hom unit evaluated on a pair of strict right DG modules. -/
@[stacks 0CS6 "DG-module derived Hom unit component"]
noncomputable abbrev unitApp (A : CochainDGAlgebra.{u, v} R)
    (M N : DifferentialGradedModule.{u, v} A) :=
  (unit A).app
    (Opposite.op ((DifferentialGradedModule.toK A).obj M),
      (DifferentialGradedModule.toK A).obj N)

/-- For a property-(I) target, the universal map from the strict Hom complex to derived Hom is
an isomorphism. -/
@[stacks 070Y "property-I derived-Hom unit isomorphism"]
theorem unitApp_isIso_of_propertyI (A : CochainDGAlgebra.{u, v} R)
    (M I : DifferentialGradedModule.{u, v} A)
    (hI : DifferentialGradedModule.HasPropertyI A I) :
    IsIso (unitApp A M I) := sorry

/-- The canonical isomorphism from the strict Hom-complex model with property-(I) target to
derived Hom. -/
@[stacks 070Y "property-I strict model of derived Hom"]
noncomputable def unitAppIsoOfPropertyI (A : CochainDGAlgebra.{u, v} R)
    (M I : DifferentialGradedModule.{u, v} A)
    (hI : DifferentialGradedModule.HasPropertyI A I) :=
  @asIso _ _ _ _ (unitApp A M I)
    (unitApp_isIso_of_propertyI A M I hI)

/-- The canonical replacement of a pair `(M, N)` by `(M, I)` along a property-(I)
resolution of the covariant entry. -/
@[stacks 09KU "property-I replacement for derived Hom"]
def replacement (A : CochainDGAlgebra.{u, v} R)
    (M : DifferentialGradedModule.{u, v} A)
    {N : DifferentialGradedModule.{u, v} A}
    (I : DifferentialGradedModule.PropertyI.Resolution A N) :
    (Opposite.op ((DifferentialGradedModule.toK A).obj M),
        (DifferentialGradedModule.toK A).obj N) ⟶
      (Opposite.op ((DifferentialGradedModule.toK A).obj M),
        (DifferentialGradedModule.toK A).obj I.obj) :=
  (𝟙 _, (DifferentialGradedModule.toK A).map I.ι)

/-- The canonical property-(I) replacement is a simultaneous quasi-isomorphism. -/
@[stacks 09KU "property-I replacement is a derived-Hom denominator"]
theorem replacement_mem (A : CochainDGAlgebra.{u, v} R)
    (M : DifferentialGradedModule.{u, v} A)
    {N : DifferentialGradedModule.{u, v} A}
    (I : DifferentialGradedModule.PropertyI.Resolution A N) :
    qis A (replacement A M I) := sorry

/-- A property-(I) resolution gives the canonical strict Hom-complex model of derived Hom. -/
@[stacks 0CS6 "property-I resolution model of DG derived Hom"]
noncomputable def resolutionModelIso (A : CochainDGAlgebra.{u, v} R)
    (M : DifferentialGradedModule.{u, v} A)
    {N : DifferentialGradedModule.{u, v} A}
    (I : DifferentialGradedModule.PropertyI.Resolution A N) :
    DerivedCategory.Q.obj (DifferentialGradedCategory.homComplex M I.obj) ≅
      (functor A).obj
        (Opposite.op
            ((DifferentialGradedModule.Derived.Q A).obj
              ((DifferentialGradedModule.toK A).obj M)),
          (DifferentialGradedModule.Derived.Q A).obj
            ((DifferentialGradedModule.toK A).obj N)) :=
  Functor.RightDerived.ComputesAt.replacementIso
    (source A) (qis A) (localization A) (replacement A M I)
    (replacement_mem A M I)
    (computesAt_of_propertyI A M I.obj
      (DifferentialGradedModule.PropertyI.Resolution.propertyI_obj A I))

/-- The forward property-(I) resolution-model isomorphism is the derived-Hom unit followed by
transport against the localized replacement. -/
@[simp]
theorem resolutionModelIso_hom (A : CochainDGAlgebra.{u, v} R)
    (M : DifferentialGradedModule.{u, v} A)
    {N : DifferentialGradedModule.{u, v} A}
    (I : DifferentialGradedModule.PropertyI.Resolution A N) :
    (resolutionModelIso A M I).hom =
      unitApp A M I.obj ≫
        (functor A).map
          (Localization.isoOfHom (localization A) (qis A)
            (replacement A M I) (replacement_mem A M I)).inv := sorry

/-- The inverse property-(I) resolution-model isomorphism transports along the localized
replacement before applying the inverse property-(I) unit isomorphism. -/
@[simp]
theorem resolutionModelIso_inv (A : CochainDGAlgebra.{u, v} R)
    (M : DifferentialGradedModule.{u, v} A)
    {N : DifferentialGradedModule.{u, v} A}
    (I : DifferentialGradedModule.PropertyI.Resolution A N) :
    (resolutionModelIso A M I).inv =
      (functor A).map
          (Localization.isoOfHom (localization A) (qis A)
            (replacement A M I) (replacement_mem A M I)).hom ≫
        (unitAppIsoOfPropertyI A M I.obj
          (DifferentialGradedModule.PropertyI.Resolution.propertyI_obj A I)).inv := sorry

/-- A pair whose contravariant entry has property (P) already computes simultaneous derived
Hom; no replacement of either displayed DG module is needed. -/
@[stacks 0BYW "property-P computation of derived Hom"]
theorem computesAt_of_propertyP (A : CochainDGAlgebra.{u, v} R)
    (M N : DifferentialGradedModule.{u, v} A)
    (hM : DifferentialGradedModule.HasPropertyP A M) :
    Functor.RightDerived.ComputesAt (source A) (qis A)
      (Opposite.op ((DifferentialGradedModule.toK A).obj M),
        (DifferentialGradedModule.toK A).obj N) := sorry

/-- For a property-(P) source, the universal map from the strict Hom complex to derived Hom is
an isomorphism. -/
@[stacks 0BYW "property-P derived-Hom unit isomorphism"]
theorem unitApp_isIso_of_propertyP (A : CochainDGAlgebra.{u, v} R)
    (M N : DifferentialGradedModule.{u, v} A)
    (hM : DifferentialGradedModule.HasPropertyP A M) :
    IsIso (unitApp A M N) := sorry

/-- The canonical isomorphism from the strict Hom-complex model of a property-(P) source to
derived Hom. -/
@[stacks 0BYW "property-P strict model of derived Hom"]
noncomputable def unitAppIsoOfPropertyP (A : CochainDGAlgebra.{u, v} R)
    (M N : DifferentialGradedModule.{u, v} A)
    (hM : DifferentialGradedModule.HasPropertyP A M) :=
  @asIso _ _ _ _ (unitApp A M N)
    (unitApp_isIso_of_propertyP A M N hM)

end DifferentialGradedModule.Derived.RHom
