module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.CommAlg.DifferentialGraded
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Grothendieck
public import ReasLib.Algebra.Homology.CochainComplex.DifferentialGraded.HomComplex.Derived.Over
public import ReasLib.Algebra.Homology.CochainComplex.DifferentialGraded.Homotopy.Derived
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Localization

/-!
# Derived module sheaves over an algebra sheaf

If `O` is a sheaf of commutative `R`-algebras, its module sheaves form a canonical `R`-linear
category.  This leaf specializes the generic enriched cochain localization and derived Hom API
to that category.  `SheafOfModules.CommAlg.Complex` remains the unique owner of the complex type;
the declarations here only expose its homotopy and derived presentations.
-/

@[expose] public section

noncomputable section

universe r u v w z

open CategoryTheory
open CategoryTheory.CochainComplex
open DifferentialGradedCategory
open scoped DifferentialGradedCategory
open scoped SheafOfModules.CommAlg
open scoped CategoryTheory.CochainComplex.Enriched.Over

namespace SheafOfModules.CommAlg.Derived

variable {R : Type r} [CommRing R]
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ (CommAlgCat.{w} R) CommRingCat.{w})]
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [UnivLE.{max u v, z}]
variable (O : Sheaf J (CommAlgCat.{w} R))

/-- The enriched-to-ordinary homotopy comparison for module-sheaf cochain complexes over `O`. -/
@[stacks 09JQ "module-sheaf enriched homotopy comparison"]
abbrev homotopy :
    DifferentialGradedCategory.K R (Complex.{r, u, v, w, z} O) ⥤
      HomotopyCategory (Modules.{r, u, v, w, z} O) (ComplexShape.up ℤ) :=
  CategoryTheory.CochainComplex.Enriched.Over.toMathlib (R := R)

/-- The canonical localization of the enriched homotopy category of `O`-module complexes. -/
@[stacks 09KX "module-sheaf enriched derived comparison"]
abbrev Q :
    DifferentialGradedCategory.K R (Complex.{r, u, v, w, z} O) ⥤
      DerivedCategory.{max (max (max u v) w) (z + 1)}
        (Modules.{r, u, v, w, z} O) :=
  CategoryTheory.CochainComplex.Enriched.Over.derivedQ (R := R)

/-- The enriched localization of a strict complex agrees with its standard derived image. -/
@[stacks 09KX "module-sheaf enriched localization object comparison"]
noncomputable abbrev objIso (K : Complex.{r, u, v, w, z} O) :
    (Q O).obj (⟨K⟩ : DifferentialGradedCategory.K R (Complex O)) ≅
      DerivedCategory.Q.obj K :=
  CategoryTheory.CochainComplex.Enriched.Over.derivedQObjIso (R := R) K

/-- The enriched homotopy-to-derived functor is the localization at quasi-isomorphisms. -/
@[stacks 09KX "module-sheaf enriched derived localization"]
noncomputable instance qIsLocalization :
    (Q O).IsLocalization
      (CategoryTheory.CochainComplex.Enriched.Over.quasiIso
        (R := R) (A := Modules.{r, u, v, w, z} O)) :=
  CategoryTheory.CochainComplex.Enriched.Over.derivedQIsLocalization

namespace RHom

/-- The homotopy-level enriched Hom source for complexes of `O`-modules. -/
@[stacks 0CS6 "module-sheaf enriched Hom source over a base ring"]
noncomputable abbrev source :=
  CategoryTheory.CochainComplex.Enriched.Over.RHom.source
    (R := R) (C := Modules.{r, u, v, w, z} O)

/-- The product quasi-isomorphism property used to derive enriched Hom of `O`-modules. -/
@[stacks 0CS6 "module-sheaf enriched Hom quasi-isomorphisms"]
abbrev qis :=
  CategoryTheory.CochainComplex.Enriched.Over.RHom.qis
    (R := R) (C := Modules.{r, u, v, w, z} O)

/-- The product localization from enriched homotopy pairs to pairs of derived `O`-modules. -/
@[stacks 0CS6 "module-sheaf enriched Hom product localization"]
noncomputable abbrev localization :=
  CategoryTheory.CochainComplex.Enriched.Over.RHom.localization
    (R := R) (C := Modules.{r, u, v, w, z} O)

/-- The existence condition for total derived enriched Hom of `O`-modules. -/
@[stacks 0CS6 "existence of module-sheaf derived enriched Hom"]
abbrev Has : Prop :=
  CategoryTheory.CochainComplex.Enriched.Over.RHom.Has
    (R := R) (C := Modules.{r, u, v, w, z} O)

variable [Has O]

/-- The total derived enriched Hom bifunctor for `O`-modules, valued in `D(R)`. -/
@[stacks 0CS6 "module-sheaf derived enriched Hom bifunctor"]
noncomputable abbrev functor :=
  CategoryTheory.CochainComplex.Enriched.Over.RHom.functor
    (R := R) (C := Modules.{r, u, v, w, z} O)

/-- The curried total derived enriched Hom functor, with source variable first. -/
@[stacks 0CS6 "curried module-sheaf derived enriched Hom"]
noncomputable abbrev curried :=
  CategoryTheory.CochainComplex.Enriched.Over.RHom.curried
    (R := R) (C := Modules.{r, u, v, w, z} O)

/-- Total derived enriched Hom with a fixed target `O`-module. -/
@[stacks 0CS6 "source-variable module-sheaf derived enriched Hom"]
noncomputable abbrev sourceFunctor
    (N : DerivedCategory.{max (max (max u v) w) (z + 1)} (Modules O)) :=
  CategoryTheory.CochainComplex.Enriched.Over.RHom.sourceFunctor
    (R := R) (C := Modules.{r, u, v, w, z} O) N

/-- Total derived enriched Hom with a fixed source `O`-module. -/
@[stacks 0CS6 "target-variable module-sheaf derived enriched Hom"]
noncomputable abbrev targetFunctor
    (M : (DerivedCategory.{max (max (max u v) w) (z + 1)} (Modules O))ᵒᵖ) :=
  CategoryTheory.CochainComplex.Enriched.Over.RHom.targetFunctor
    (R := R) (C := Modules.{r, u, v, w, z} O) M

/-- The universal map from strict enriched Hom to total derived enriched Hom. -/
@[stacks 0CS6 "unit for module-sheaf derived enriched Hom"]
noncomputable abbrev unit :=
  CategoryTheory.CochainComplex.Enriched.Over.RHom.unit
    (R := R) (C := Modules.{r, u, v, w, z} O)

/-- The derived-Hom unit evaluated on two strict complexes of `O`-modules. -/
@[stacks 0CS6 "strict-complex component of module-sheaf derived Hom"]
noncomputable abbrev unitApp (M N : Complex.{r, u, v, w, z} O) :=
  CategoryTheory.CochainComplex.Enriched.Over.RHom.unitApp
    (R := R) (C := Modules.{r, u, v, w, z} O) M N

/-- The strict-complex derived-Hom unit is invertible when the target is K-injective. -/
@[stacks 070Y "module-sheaf K-injective derived-Hom unit criterion"]
abbrev unitApp_isIso_of_kInjective
    (M I : Complex.{r, u, v, w, z} O) [I.IsKInjective] :
    IsIso (unitApp O M I) :=
  CategoryTheory.CochainComplex.Enriched.Over.RHom.unitApp_isIso_of_kInjective
    (R := R) (C := Modules.{r, u, v, w, z} O) M I

/-- Strict enriched Hom into a K-injective target computes derived Hom. -/
@[stacks 070Y "K-injective model of module-sheaf derived Hom"]
noncomputable abbrev unitAppIsoOfKInjective
    (M I : Complex.{r, u, v, w, z} O) [I.IsKInjective] :=
  CategoryTheory.CochainComplex.Enriched.Over.RHom.unitAppIsoOfKInjective
    (R := R) (C := Modules.{r, u, v, w, z} O) M I

/-- Replace the covariant complex by a chosen K-injective resolution in the product homotopy
category. -/
@[stacks 090Y "module-sheaf K-injective replacement"]
abbrev replacement
    (M : Complex.{r, u, v, w, z} O) {N : Complex.{r, u, v, w, z} O}
    (I : CochainComplex.KInjectiveResolution N) :
    (Opposite.op
        (⟨M⟩ : DifferentialGradedCategory.K R (Complex O)),
      (⟨N⟩ : DifferentialGradedCategory.K R (Complex O))) ⟶
      (Opposite.op
        (⟨M⟩ : DifferentialGradedCategory.K R (Complex O)),
      (⟨I.complex⟩ : DifferentialGradedCategory.K R (Complex O))) :=
  CategoryTheory.CochainComplex.Enriched.Over.RHom.replacement
    (R := R) (C := Modules.{r, u, v, w, z} O) M I

/-- A K-injective replacement is a denominator for the derived-Hom localization. -/
@[stacks 090Y "module-sheaf K-injective replacement denominator"]
abbrev replacement_mem
    (M : Complex.{r, u, v, w, z} O) {N : Complex.{r, u, v, w, z} O}
    (I : CochainComplex.KInjectiveResolution N) :
    qis O (replacement O M I) :=
  CategoryTheory.CochainComplex.Enriched.Over.RHom.replacement_mem
    (R := R) (C := Modules.{r, u, v, w, z} O) M I

/-- A K-injective resolution gives the strict enriched-Hom model of derived Hom. -/
@[stacks 0CS6 "K-injective resolution model of module-sheaf derived Hom"]
noncomputable abbrev resolutionModelIso
    (M : Complex.{r, u, v, w, z} O) {N : Complex.{r, u, v, w, z} O}
    (I : CochainComplex.KInjectiveResolution N) :=
  CategoryTheory.CochainComplex.Enriched.Over.RHom.resolutionModelIso
    (R := R) (C := Modules.{r, u, v, w, z} O) M I

/-- The forward map of the module-sheaf K-injective resolution comparison. -/
@[stacks 0CS6 "forward module-sheaf resolution comparison"]
abbrev resolutionModelIso_hom
    (M : Complex.{r, u, v, w, z} O) {N : Complex.{r, u, v, w, z} O}
    (I : CochainComplex.KInjectiveResolution N) :
    (resolutionModelIso O M I).hom =
      unitApp O M I.complex ≫
        (functor O).map
          (CategoryTheory.Localization.isoOfHom (localization O) (qis O)
            (replacement O M I) (replacement_mem O M I)).inv ≫
        (functor O).map
          (Iso.prod
            (CategoryTheory.CochainComplex.Enriched.Over.derivedQObjIso
              (R := R) (A := Modules.{r, u, v, w, z} O) M).symm.op
            (CategoryTheory.CochainComplex.Enriched.Over.derivedQObjIso
              (R := R) (A := Modules.{r, u, v, w, z} O) N)).hom :=
  CategoryTheory.CochainComplex.Enriched.Over.RHom.resolutionModelIso_hom
    (R := R) (C := Modules.{r, u, v, w, z} O) M I

/-- The inverse map of the module-sheaf K-injective resolution comparison. -/
@[stacks 0CS6 "inverse module-sheaf resolution comparison"]
abbrev resolutionModelIso_inv
    (M : Complex.{r, u, v, w, z} O) {N : Complex.{r, u, v, w, z} O}
    (I : CochainComplex.KInjectiveResolution N) :
    (resolutionModelIso O M I).inv =
      (functor O).map
          (Iso.prod
            (CategoryTheory.CochainComplex.Enriched.Over.derivedQObjIso
              (R := R) (A := Modules.{r, u, v, w, z} O) M).symm.op
            (CategoryTheory.CochainComplex.Enriched.Over.derivedQObjIso
              (R := R) (A := Modules.{r, u, v, w, z} O) N)).inv ≫
        (functor O).map
          (CategoryTheory.Localization.isoOfHom (localization O) (qis O)
            (replacement O M I) (replacement_mem O M I)).hom ≫
        (unitAppIsoOfKInjective O M I.complex).inv :=
  CategoryTheory.CochainComplex.Enriched.Over.RHom.resolutionModelIso_inv
    (R := R) (C := Modules.{r, u, v, w, z} O) M I

end RHom

end SheafOfModules.CommAlg.Derived
