/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Category.DifferentialGraded.Functor.HomComplex.DerivedMap
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.TensorWithObject.Derived.Hom
public import ReasLib.Algebra.Homology.CochainComplex.KInjective.Resolution
public import ReasLib.Algebra.Homology.CochainComplex.DifferentialGraded.HomComplex.KInjective
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Derived.Hom

/-!
# A property-(P)/K-injective model of the tensor-Hom comparison

This file owns the explicit computation used for the derived Hom comparison associated to a
complex `K` on a ringed site. Property-(P) modules compute the left-derived tensor functor, while
a K-injective resolution computes global derived Hom. The resulting cochain map is concrete and
does not depend on a global choice of resolutions.

The model is kept separate from the abstract source and target bifunctors.  The named source and
target model isomorphisms identify its concrete comparison with the descended transformation on
arbitrary derived DG modules.  This must not be confused with right-deriving
`Hom(F(-), F(-))` in both variables.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory
open DifferentialGradedCategory
open scoped DifferentialGradedCategory

namespace SheafOfModules.RingedSite.TensorWithObject.Derived.Hom.Model

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable {O : Sheaf J CommRingCat.{max u v}}

open DifferentialGradedCategory.HomComplex

/-- A property-(P) source model for `RHom` of two right DG modules, as an object of `D(ℤ)`. -/
@[stacks 0CS6 "property-P source model for the derived Hom comparison"]
abbrev source (K : Complex (J := J) (O := O)) (M N : Modules K) :
    DerivedCategory (ModuleCat.{max u v} ℤ) :=
  DifferentialGradedCategory.HomComplex.derived M N

/-- A K-injective target model for global `RHom` from the tensor image of `M` to the tensor image
of `N`, as an object of `D(ℤ)`. -/
@[stacks 0CS6 "K-injective target model for the derived Hom comparison"]
abbrev target (K : Complex (J := J) (O := O)) (M N : Modules K)
    (I : CochainComplex.KInjectiveResolution ((TensorWithObject.tensorFunctor K).obj N)) :
    DerivedCategory (ModuleCat.{max u v} ℤ) :=
  DifferentialGradedCategory.HomComplex.derived
    ((TensorWithObject.tensorFunctor K).obj M) I.complex

/-- Property-(P) tensor models and a K-injective resolution identify the explicit target Hom
complex with global derived Hom of the two derived tensor values. -/
@[stacks 0CS6 "target model of the derived tensor-Hom comparison"]
noncomputable def targetModelIso (K : Complex (J := J) (O := O))
    (M N : Modules K)
    (I : CochainComplex.KInjectiveResolution
      ((TensorWithObject.tensorFunctor K).obj N))
    (hM : DifferentialGradedModule.HasPropertyP (endDGA K) M)
    (hN : DifferentialGradedModule.HasPropertyP (endDGA K) N) :
    target K M N I ≅
      (Target.functor K).obj
        (Opposite.op
            ((DifferentialGradedModule.Derived.fromModules (endDGA K)).obj M),
          (DifferentialGradedModule.Derived.fromModules (endDGA K)).obj N) :=
  RingedSite.Hom.ModuleDerived.RHom.maxResolutionModelIso J O
      ((TensorWithObject.tensorFunctor K).obj M)
      I ≪≫
    (RingedSite.Hom.ModuleDerived.RHom.maxFunctor J O).mapIso
        (Iso.prod (tensorModelIso K M hM).op
          (tensorModelIso K N hN).symm)

/-- The forward target-model comparison is resolution followed by transport along the tensor
models. -/
@[simp, stacks 0CS6 "forward target-model comparison"]
theorem targetModelIso_hom (K : Complex (J := J) (O := O))
    (M N : Modules K)
    (I : CochainComplex.KInjectiveResolution
      ((TensorWithObject.tensorFunctor K).obj N))
    (hM : DifferentialGradedModule.HasPropertyP (endDGA K) M)
    (hN : DifferentialGradedModule.HasPropertyP (endDGA K) N) :
    (targetModelIso K M N I hM hN).hom =
      (RingedSite.Hom.ModuleDerived.RHom.maxResolutionModelIso J O
        ((TensorWithObject.tensorFunctor K).obj M) I).hom ≫
        ((RingedSite.Hom.ModuleDerived.RHom.maxFunctor J O).mapIso
          (Iso.prod (tensorModelIso K M hM).op
            (tensorModelIso K N hN).symm)).hom := sorry

/-- The inverse target-model comparison reverses tensor-model transport and resolution. -/
@[simp, stacks 0CS6 "inverse target-model comparison"]
theorem targetModelIso_inv (K : Complex (J := J) (O := O))
    (M N : Modules K)
    (I : CochainComplex.KInjectiveResolution
      ((TensorWithObject.tensorFunctor K).obj N))
    (hM : DifferentialGradedModule.HasPropertyP (endDGA K) M)
    (hN : DifferentialGradedModule.HasPropertyP (endDGA K) N) :
    (targetModelIso K M N I hM hN).inv =
      ((RingedSite.Hom.ModuleDerived.RHom.maxFunctor J O).mapIso
          (Iso.prod (tensorModelIso K M hM).op
            (tensorModelIso K N hN).symm)).inv ≫
        (RingedSite.Hom.ModuleDerived.RHom.maxResolutionModelIso J O
          ((TensorWithObject.tensorFunctor K).obj M) I).inv := sorry

/-- Apply the tensor DG functor to an enriched Hom complex, then postcompose with the chosen
K-injective resolution map. -/
@[stacks 0CS6 "property-P K-injective cochain comparison"]
def cochainMap (K : Complex (J := J) (O := O)) (M N : Modules K)
    (I : CochainComplex.KInjectiveResolution ((TensorWithObject.tensorFunctor K).obj N)) :
    DifferentialGradedCategory.homComplex M N ⟶
      DifferentialGradedCategory.homComplex
        ((TensorWithObject.tensorFunctor K).obj M) I.complex :=
  mapPostcomp (TensorWithObject.tensorFunctor K) M N
    (CochainComplex.Enriched.ofHom I.ι)

/-- The concrete morphism in `D(ℤ)` from a property-(P) source Hom model to a chosen
K-injective global Hom model after tensoring with `K`. -/
@[stacks 0CS6 "property-P/K-injective model of the derived Hom comparison"]
def comparison (K : Complex (J := J) (O := O)) (M N : Modules K)
    (I : CochainComplex.KInjectiveResolution ((TensorWithObject.tensorFunctor K).obj N)) :
    source K M N ⟶ target K M N I :=
  derivedMapPostcomp (TensorWithObject.tensorFunctor K) M N
    (CochainComplex.Enriched.ofHom I.ι)

/-- The explicit property-(P)/K-injective cochain-map model computes the abstract comparison on
the corresponding derived DG modules. -/
@[reassoc, stacks 0CS6 "model computation of the derived tensor-Hom comparison"]
theorem comparison_fac (K : Complex (J := J) (O := O))
    (M N : Modules K)
    (I : CochainComplex.KInjectiveResolution
      ((TensorWithObject.tensorFunctor K).obj N))
    (hM : DifferentialGradedModule.HasPropertyP (endDGA K) M)
    (hN : DifferentialGradedModule.HasPropertyP (endDGA K) N) :
    comparison K M N I ≫ (targetModelIso K M N I hM hN).hom =
      (DifferentialGradedModule.Derived.RHom.unitAppIsoOfPropertyP
          (endDGA K) M N hM).hom ≫
        comparisonApp K
          ((DifferentialGradedModule.Derived.fromModules (endDGA K)).obj M)
          ((DifferentialGradedModule.Derived.fromModules (endDGA K)).obj N) := sorry

/-- The model comparison is contravariantly natural in its source module. -/
@[reassoc, stacks 0CS6 "source naturality of the model Hom comparison"]
theorem comparison_naturality_source
    (K : Complex (J := J) (O := O)) {M M' N : Modules K}
    (f : CompHom M' M)
    (I : CochainComplex.KInjectiveResolution ((TensorWithObject.tensorFunctor K).obj N)) :
    DerivedCategory.Q.map (precomp f) ≫ comparison K M' N I =
      comparison K M N I ≫
        DerivedCategory.Q.map
          (precomp ((TensorWithObject.tensorFunctor K).mapCompHom f)) := sorry

/-- The model comparison is covariantly natural in the target module and in compatible maps of
its K-injective resolutions. -/
@[reassoc, stacks 0CS6 "target naturality of the model Hom comparison"]
theorem comparison_naturality_target
    (K : Complex (J := J) (O := O)) {M N N' : Modules K}
    (g : CompHom N N')
    (I : CochainComplex.KInjectiveResolution ((TensorWithObject.tensorFunctor K).obj N))
    (I' : CochainComplex.KInjectiveResolution ((TensorWithObject.tensorFunctor K).obj N'))
    (j : I.complex ⟶ I'.complex)
    (comm : CochainComplex.Enriched.toHom
        ((TensorWithObject.tensorFunctor K).mapCompHom g) ≫ I'.ι = I.ι ≫ j) :
    DerivedCategory.Q.map (postcomp g) ≫ comparison K M N' I' =
      comparison K M N I ≫
        DerivedCategory.Q.map (postcomp (CochainComplex.Enriched.ofHom j)) := sorry

/-- The map on degree-`n` cohomology induced by the explicit model comparison. -/
@[stacks 0CS6 "cohomology map of the model Hom comparison"]
noncomputable def cohomologyMap (K : Complex (J := J) (O := O))
    (M N : Modules K)
    (I : CochainComplex.KInjectiveResolution ((TensorWithObject.tensorFunctor K).obj N))
    (n : ℤ) :
    (DifferentialGradedCategory.homComplex M N).homology n ⟶
      (DifferentialGradedCategory.homComplex
        ((TensorWithObject.tensorFunctor K).obj M) I.complex).homology n :=
  cohomologyMapPostcomp (TensorWithObject.tensorFunctor K) M N
    (CochainComplex.Enriched.ofHom I.ι) n

/-- The explicit model map forms the canonical comparison square with the derived tensor functor
and its counit. For property-(P) inputs, `tensorCounitApp_isIso` turns the two vertical sides into
the usual Ext identifications. -/
@[stacks 0CS6 "cohomology of the property-P/K-injective Hom comparison"]
theorem cohomologyMap_shiftedHom (K : Complex (J := J) (O := O))
    (M N : Modules K)
    (I : CochainComplex.KInjectiveResolution ((TensorWithObject.tensorFunctor K).obj N))
    (n : ℤ) (x : (DifferentialGradedCategory.homComplex M N).homology n) :
    (tensorCounit K).app
          ((DifferentialGradedModule.toK (endDGA K)).obj M) ≫
        CochainComplex.Enriched.injectiveDerivedHomLinearMap
          ((TensorWithObject.tensorFunctor K).obj M)
          ((TensorWithObject.tensorFunctor K).obj N) I.complex I.ι n
          (cohomologyMap K M N I n x) =
      ShiftedHom.map
          (DifferentialGradedModule.Derived.homologyHomLinearMap M N n x)
          (tensorFunctor K) ≫
        (shiftFunctor _ n).map
          ((tensorCounit K).app
            ((DifferentialGradedModule.toK (endDGA K)).obj N)) := sorry

end SheafOfModules.RingedSite.TensorWithObject.Derived.Hom.Model
