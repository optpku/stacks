/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Category.DifferentialGraded.Functor.HomComplex.DerivedMap
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.CommAlg.TensorWithObject.Derived.Hom
public import ReasLib.Algebra.Homology.CochainComplex.DifferentialGraded.HomComplex.KInjective.Over
public import ReasLib.Algebra.Homology.CochainComplex.KInjective.Resolution
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Derived.Hom

/-!
# A property-(P)/K-injective model of the algebra-sheaf tensor-Hom comparison

This leaf computes the coefficient-generic derived tensor-Hom comparison on explicit models.
Property-(P) modules compute derived tensoring, while a chosen K-injective resolution computes
the target derived `RHom`.  No global choice of resolutions is made.
-/

@[expose] public section

noncomputable section

universe r u v w z

open CategoryTheory
open DifferentialGradedCategory
open DifferentialGradedCategory.HomComplex
open scoped DifferentialGradedCategory SheafOfModules.CommAlg

namespace SheafOfModules.CommAlg.TensorWithObject.Derived.Hom.Model

variable {R : Type r} [CommRing R]
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ (CommAlgCat.{w} R) CommRingCat.{w})]
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [UnivLE.{max u v, max u z}]
variable [HasWeakSheafify J AddCommGrpCat.{max u z}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u z}]
variable {O : Sheaf J (CommAlgCat.{w} R)}

/-- A property-(P) source model for derived Hom of two right DG modules. -/
@[stacks 0CS6 "arbitrary-ring property-P source Hom model"]
abbrev source (K : Complex.{r, u, v, w, max u z} O) (M N : Modules K) :
    DerivedCategory (ModuleCat.{max u z} R) :=
  DifferentialGradedCategory.HomComplex.derived M N

/-- A K-injective target model for derived Hom after tensoring both variables with `K`. -/
@[stacks 0CS6 "arbitrary-ring K-injective target Hom model"]
abbrev target (K : Complex.{r, u, v, w, max u z} O) (M N : Modules K)
    (I : CochainComplex.KInjectiveResolution ((TensorWithObject.tensorFunctor K).obj N)) :
    DerivedCategory (ModuleCat.{max u z} R) :=
  DifferentialGradedCategory.HomComplex.derived
    ((TensorWithObject.tensorFunctor K).obj M) I.complex

section DerivedHom

variable [SheafOfModules.CommAlg.Derived.RHom.Has.{r, u, v, w, max u z} O]

/-- Property-(P) tensor models and a K-injective resolution identify the explicit target with
derived `RHom` of the two derived tensor values. -/
@[stacks 0CS6 "arbitrary-ring target model of the tensor-Hom comparison"]
noncomputable def targetModelIso (K : Complex.{r, u, v, w, max u z} O)
    (M N : Modules K)
    (I : CochainComplex.KInjectiveResolution ((TensorWithObject.tensorFunctor K).obj N))
    (hM : DifferentialGradedModule.HasPropertyP (endDGA K) M)
    (hN : DifferentialGradedModule.HasPropertyP (endDGA K) N) :
    target K M N I ≅
      (Target.functor K).obj
        (Opposite.op
            ((DifferentialGradedModule.Derived.fromModules (endDGA K)).obj M),
          (DifferentialGradedModule.Derived.fromModules (endDGA K)).obj N) :=
  SheafOfModules.CommAlg.Derived.RHom.resolutionModelIso
      O ((TensorWithObject.tensorFunctor K).obj M) I ≪≫
    (SheafOfModules.CommAlg.Derived.RHom.functor O).mapIso
      (Iso.prod
        (SheafOfModules.CommAlg.TensorWithObject.Derived.tensorModelIso K M hM).op
        (SheafOfModules.CommAlg.TensorWithObject.Derived.tensorModelIso K N hN).symm)

/-- The forward target-model comparison is the resolution comparison followed by derived transport.
-/
@[reassoc (attr := simp), stacks 0CS6 "forward target-model comparison"]
theorem targetModelIso_hom (K : Complex.{r, u, v, w, max u z} O)
    (M N : Modules K)
    (I : CochainComplex.KInjectiveResolution ((TensorWithObject.tensorFunctor K).obj N))
    (hM : DifferentialGradedModule.HasPropertyP (endDGA K) M)
    (hN : DifferentialGradedModule.HasPropertyP (endDGA K) N) :
    (targetModelIso K M N I hM hN).hom =
      (SheafOfModules.CommAlg.Derived.RHom.resolutionModelIso
          O ((TensorWithObject.tensorFunctor K).obj M) I).hom ≫
        ((SheafOfModules.CommAlg.Derived.RHom.functor O).mapIso
          (Iso.prod
            (SheafOfModules.CommAlg.TensorWithObject.Derived.tensorModelIso K M hM).op
            (SheafOfModules.CommAlg.TensorWithObject.Derived.tensorModelIso K N hN).symm)).hom := sorry

/-- The inverse target-model comparison reverses the derived transport and resolution comparison.
-/
@[reassoc (attr := simp), stacks 0CS6 "inverse target-model comparison"]
theorem targetModelIso_inv (K : Complex.{r, u, v, w, max u z} O)
    (M N : Modules K)
    (I : CochainComplex.KInjectiveResolution ((TensorWithObject.tensorFunctor K).obj N))
    (hM : DifferentialGradedModule.HasPropertyP (endDGA K) M)
    (hN : DifferentialGradedModule.HasPropertyP (endDGA K) N) :
    (targetModelIso K M N I hM hN).inv =
      ((SheafOfModules.CommAlg.Derived.RHom.functor O).mapIso
          (Iso.prod
            (SheafOfModules.CommAlg.TensorWithObject.Derived.tensorModelIso K M hM).op
            (SheafOfModules.CommAlg.TensorWithObject.Derived.tensorModelIso K N hN).symm)).inv ≫
        (SheafOfModules.CommAlg.Derived.RHom.resolutionModelIso
          O ((TensorWithObject.tensorFunctor K).obj M) I).inv := sorry

end DerivedHom

/-- Apply the tensor DG functor to an enriched Hom complex, then postcompose with the chosen
K-injective resolution map. -/
@[stacks 0CS6 "arbitrary-ring property-P K-injective cochain comparison"]
def cochainMap (K : Complex.{r, u, v, w, max u z} O) (M N : Modules K)
    (I : CochainComplex.KInjectiveResolution ((TensorWithObject.tensorFunctor K).obj N)) :
    homComplex M N ⟶
      homComplex ((TensorWithObject.tensorFunctor K).obj M) I.complex :=
  mapPostcomp (TensorWithObject.tensorFunctor K) M N
    (CategoryTheory.CochainComplex.Enriched.Over.ofHom
      (R := R)
      (C := SheafOfModules.CommAlg.Modules.{r, u, v, w, max u z} O) I.ι)

/-- The concrete morphism from the property-(P) source model to the K-injective target model. -/
@[stacks 0CS6 "arbitrary-ring property-P/K-injective Hom comparison"]
def comparison (K : Complex.{r, u, v, w, max u z} O) (M N : Modules K)
    (I : CochainComplex.KInjectiveResolution ((TensorWithObject.tensorFunctor K).obj N)) :
    source K M N ⟶ target K M N I :=
  derivedMapPostcomp (TensorWithObject.tensorFunctor K) M N
    (CategoryTheory.CochainComplex.Enriched.Over.ofHom
      (R := R)
      (C := SheafOfModules.CommAlg.Modules.{r, u, v, w, max u z} O) I.ι)

section DerivedHom

variable [SheafOfModules.CommAlg.Derived.RHom.Has.{r, u, v, w, max u z} O]

/-- The concrete property-(P)/K-injective map computes the descended comparison. -/
@[reassoc, stacks 0CS6 "model computation of the arbitrary-ring tensor-Hom comparison"]
theorem comparison_fac (K : Complex.{r, u, v, w, max u z} O)
    (M N : Modules K)
    (I : CochainComplex.KInjectiveResolution ((TensorWithObject.tensorFunctor K).obj N))
    (hM : DifferentialGradedModule.HasPropertyP (endDGA K) M)
    (hN : DifferentialGradedModule.HasPropertyP (endDGA K) N) :
    comparison K M N I ≫ (targetModelIso K M N I hM hN).hom =
      (DifferentialGradedModule.Derived.RHom.unitAppIsoOfPropertyP
          (endDGA K) M N hM).hom ≫
        Hom.comparisonApp K
          ((DifferentialGradedModule.Derived.fromModules (endDGA K)).obj M)
          ((DifferentialGradedModule.Derived.fromModules (endDGA K)).obj N) := sorry

end DerivedHom

/-- The model comparison is contravariantly natural in the source module. -/
@[reassoc, stacks 0CS6 "source naturality of the arbitrary-ring model comparison"]
theorem comparison_naturality_source
    (K : Complex.{r, u, v, w, max u z} O) {M M' N : Modules K}
    (f : CompHom M' M)
    (I : CochainComplex.KInjectiveResolution ((TensorWithObject.tensorFunctor K).obj N)) :
    DerivedCategory.Q.map (precomp f) ≫ comparison K M' N I =
      comparison K M N I ≫
        DerivedCategory.Q.map
          (precomp ((TensorWithObject.tensorFunctor K).mapCompHom f)) := sorry

/-- The model comparison is covariantly natural in the target and in compatible resolution
maps. -/
@[reassoc, stacks 0CS6 "target naturality of the arbitrary-ring model comparison"]
theorem comparison_naturality_target
    (K : Complex.{r, u, v, w, max u z} O) {M N N' : Modules K}
    (g : CompHom N N')
    (I : CochainComplex.KInjectiveResolution ((TensorWithObject.tensorFunctor K).obj N))
    (I' : CochainComplex.KInjectiveResolution ((TensorWithObject.tensorFunctor K).obj N'))
    (j : I.complex ⟶ I'.complex)
    (comm : CategoryTheory.CochainComplex.Enriched.Over.toHom
        (R := R)
        (C := SheafOfModules.CommAlg.Modules.{r, u, v, w, max u z} O)
        ((TensorWithObject.tensorFunctor K).mapCompHom g) ≫ I'.ι = I.ι ≫ j) :
    DerivedCategory.Q.map (postcomp g) ≫ comparison K M N' I' =
      comparison K M N I ≫
        DerivedCategory.Q.map
          (postcomp (CategoryTheory.CochainComplex.Enriched.Over.ofHom
            (R := R)
            (C := SheafOfModules.CommAlg.Modules.{r, u, v, w, max u z} O) j)) := sorry

/-- The map on degree-`n` cohomology induced by the explicit model comparison. -/
@[stacks 0CS6 "cohomology map of the arbitrary-ring model comparison"]
noncomputable def cohomologyMap (K : Complex.{r, u, v, w, max u z} O)
    (M N : Modules K)
    (I : CochainComplex.KInjectiveResolution ((TensorWithObject.tensorFunctor K).obj N))
    (n : ℤ) :
    (homComplex M N).homology n ⟶
      (homComplex ((TensorWithObject.tensorFunctor K).obj M) I.complex).homology n :=
  cohomologyMapPostcomp (TensorWithObject.tensorFunctor K) M N
    (CategoryTheory.CochainComplex.Enriched.Over.ofHom
      (R := R)
      (C := SheafOfModules.CommAlg.Modules.{r, u, v, w, max u z} O) I.ι) n

/-- The explicit model map forms the canonical comparison square with derived tensoring and its
counit. -/
@[stacks 0CS6 "cohomology of the arbitrary-ring property-P/K-injective comparison"]
theorem cohomologyMap_shiftedHom (K : Complex.{r, u, v, w, max u z} O)
    (M N : Modules K)
    (I : CochainComplex.KInjectiveResolution ((TensorWithObject.tensorFunctor K).obj N))
    (n : ℤ) (x : (homComplex M N).homology n) :
    (SheafOfModules.CommAlg.TensorWithObject.Derived.tensorCounit K).app
          ((DifferentialGradedModule.toK (endDGA K)).obj M) ≫
        CategoryTheory.CochainComplex.Enriched.Over.RHom.injectiveDerivedHomLinearMap
          (R := R) ((TensorWithObject.tensorFunctor K).obj M) I.ι n
          (cohomologyMap K M N I n x) =
      ShiftedHom.map
          (DifferentialGradedModule.Derived.homologyHomLinearMap M N n x)
          (SheafOfModules.CommAlg.TensorWithObject.Derived.tensorFunctor K) ≫
        (shiftFunctor _ n).map
          ((SheafOfModules.CommAlg.TensorWithObject.Derived.tensorCounit K).app
            ((DifferentialGradedModule.toK (endDGA K)).obj N)) := sorry

end SheafOfModules.CommAlg.TensorWithObject.Derived.Hom.Model
