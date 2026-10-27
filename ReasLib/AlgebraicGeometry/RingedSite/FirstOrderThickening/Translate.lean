/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import ReasLib.AlgebraicGeometry.RingedSite.Module.ChangeOfRings
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Localization
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Differentials.Conormal
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Differentials.Conormal.SquareZero
public import ReasLib.AlgebraicGeometry.RingedSite.Module.NaiveCotangent.Functoriality
public import ReasLib.AlgebraicGeometry.RingedSite.Module.NaiveCotangent.Presentation.Map
public import ReasLib.AlgebraicGeometry.RingedSite.Module.NaiveCotangent.Presentation.Ext
public import ReasLib.AlgebraicGeometry.RingedSite.FirstOrderThickening.Solution
public import ReasLib.CategoryTheory.Sites.AlgebraicSheaf.FreeAlgebra.Evaluation

/-!
# Graph-quotient translations of square-zero ring-sheaf extensions

A conormal map perturbs a polynomial presentation by its graph ideal.
Representatives and invertibility of the specified coefficient inclusion are explicit inputs.
Inverse-image and sheafification comparisons use their canonical library constructions;
exposing their preservation certificates as explicit data is a further refinement of these foundations.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf
open SheafOfModules.RingedSite
open SheafOfModules.RingedSite.NaiveCotangent
open HomologicalComplex DerivedCategory
open Opposite TrivSqZeroExt
open scoped DerivedExt SheafOfModules.RingedSite
open scoped CategoryTheory.Sheaf.FreeAlgebra

noncomputable section

universe c v w

namespace SheafOfModules.RingedSite.FirstOrderThickening
namespace Solution

-- Local instance justification (defeq pin): `moduleCat_hasDerivedCategory` is reducible to `HasDerivedCategory.standard` and is not global; `ModuleDerived`, `singleFunctor`, and Ext must share that same derived-category instance.
attribute [local instance] RingedSite.Hom.moduleCat_hasDerivedCategory
-- Local instance justification (defeq pin): the commutative-sheaf presentation uses the same standard derived-category owner, exposed through the site-level spelling.
attribute [local instance] HasDerivedCategory.standard

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [J.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [HasWeakSheafify J CommRingCat.{w}]
variable [J.WEqualsLocallyBijective CommRingCat.{w}]
variable [HasSheafify J AddCommGrpCat.{w}]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable {O_B' O_B O : Sheaf J CommRingCat.{w}}
variable {π : O_B' ⟶ O_B} [Sheaf.IsLocallySurjective π]
variable {hπ : KernelIdeal.IsSquareZero π}
variable {fSharp : O_B ⟶ O}
variable {G : SheafOfModules (ringSheaf J O)}
variable {c :
    hπ.targetModule (KernelIdeal.quotientComparison_isIso π) ⟶
      (restrictionAlong fSharp).obj G}

/-- A solution supplies a locally surjective projection `proj : O' ⟶ O`. -/
theorem instIsLocallySurjective_proj (sol : Solution π hπ fSharp G c) :
    Sheaf.IsLocallySurjective sol.proj :=
  sol.proj_locallySurjective


section Of

variable (E : Sheaf J (Type w))
variable (α : E ⟶ FreeAlgebra.Presentation.generators (Under.mk fSharp))

/-- The fiber-product sheaf of sets `ℰ ×_O O'` on `C`. -/
def generatorSheaf (sol : Solution π hπ fSharp G c) : Sheaf J (Type w) :=
  Limits.pullback α ((sheafForget J).map sol.proj)

/-- `generatorSheaf` is the pullback of the polynomial generators along `sol.proj`. -/
theorem generatorSheaf_spec (sol : Solution π hπ fSharp G c) :
    generatorSheaf E α sol =
      Limits.pullback α ((sheafForget J).map sol.proj) := sorry

/-- Assignment of fiber-product generators to `O`. -/
def generatorAssign (sol : Solution π hπ fSharp G c) :
    generatorSheaf E α sol ⟶ FreeAlgebra.Presentation.generators (Under.mk fSharp) :=
  Limits.pullback.fst α ((sheafForget J).map sol.proj) ≫ α

/-- Assignment of fiber-product generators to `O'`. -/
def generatorFrontAssign (sol : Solution π hπ fSharp G c) :
    generatorSheaf E α sol ⟶ (sheafForget J).obj sol.middle :=
  Limits.pullback.snd α ((sheafForget J).map sol.proj)

/-- The polynomial algebra `O_{B'}[ℰ]`. -/
def freeAlgebraS' (sol : Solution π hπ fSharp G c) : Sheaf J CommRingCat.{w} :=
  O_B' [generatorSheaf E α sol]

/-- Evaluation `φ : O_{B'}[ℰ] ⟶ O'` on fiber-product generators. -/
def evalToMiddle (sol : Solution π hπ fSharp G c) :
    freeAlgebraS' E α sol ⟶ sol.middle :=
  (FreeAlgebra.evaluation (Under.mk sol.structureMap)
    (generatorSheaf E α sol) (generatorFrontAssign E α sol)).right

/-- Evaluation `O_{B'}[ℰ] ⟶ O` on fiber-product generators. -/
def evalToO (sol : Solution π hπ fSharp G c) :
    freeAlgebraS' E α sol ⟶ O :=
  (FreeAlgebra.evaluation (Under.mk (π ≫ fSharp))
    (generatorSheaf E α sol) (generatorAssign E α sol)).right

/-- `evalToO` is free-algebra evaluation of the fiber-product generators on `O`. -/
theorem evalToO_spec (sol : Solution π hπ fSharp G c) :
    evalToO E α sol =
      (FreeAlgebra.evaluation (Under.mk (π ≫ fSharp))
        (generatorSheaf E α sol) (generatorAssign E α sol)).right := sorry

/-- `evalToMiddle` is free-algebra evaluation of the fiber-product generators on `O'`. -/
theorem evalToMiddle_spec (sol : Solution π hπ fSharp G c) :
    evalToMiddle E α sol =
      (FreeAlgebra.evaluation (Under.mk sol.structureMap)
        (generatorSheaf E α sol) (generatorFrontAssign E α sol)).right := sorry

/-- The `O_{B'}`-polynomial presentation of `O` on the fiber-product generators. -/
def generatorCotangentS' (sol : Solution π hπ fSharp G c) :
    CochainComplex (SheafOfModules (ringSheaf J O)) ℤ :=
  Presentation.ofGenerators (B := Under.mk (π ≫ fSharp))
    (generatorSheaf E α sol) (generatorAssign E α sol)

/-- Identification of the `O_{B'}`-presentation naive cotangent with `NL(fSharp)`, via
the commutative square with base map `π` and identity on `O`. -/
def naiveCotangentS'ToF :
    NaiveCotangent.obj O_B' (Under.mk (π ≫ fSharp)) ⟶
      NaiveCotangent.obj O_B (Under.mk fSharp) :=
  (extendComplexIdIso O).inv.app (NaiveCotangent.obj O_B' (Under.mk (π ≫ fSharp))) ≫
    NaiveCotangent.map
      (⟨(Category.comp_id (π ≫ fSharp)).symm⟩ : CommSq π (π ≫ fSharp) fSharp (𝟙 O))

/-- `naiveCotangentS'ToF` is identity-extension comparison followed by the naive-cotangent
map of the square with base `π`. -/
theorem naiveCotangentS'ToF_spec :
    naiveCotangentS'ToF =
      (extendComplexIdIso O).inv.app (NaiveCotangent.obj O_B' (Under.mk (π ≫ fSharp))) ≫
        NaiveCotangent.map
          (⟨(Category.comp_id (π ≫ fSharp)).symm⟩ :
            CommSq π (π ≫ fSharp) fSharp (𝟙 O)) := sorry

/-- Presentation comparison from the `O_{B'}`-polynomial model on fiber-product generators
to `NL(fSharp)`. -/
def toCanonicalCotangent (sol : Solution π hπ fSharp G c) :
    generatorCotangentS' E α sol ⟶ NaiveCotangent.obj O_B (Under.mk fSharp) :=
  Presentation.toCanonicalMap (B := Under.mk (π ≫ fSharp))
      (generatorSheaf E α sol) (generatorAssign E α sol) ≫
    naiveCotangentS'ToF

/-- `toCanonicalCotangent` is `toCanonicalMap` of the `O_{B'}`-presentation followed by
`naiveCotangentS'ToF`. -/
theorem toCanonicalCotangent_spec (sol : Solution π hπ fSharp G c) :
    toCanonicalCotangent E α sol =
      Presentation.toCanonicalMap (B := Under.mk (π ≫ fSharp))
          (generatorSheaf E α sol) (generatorAssign E α sol) ≫
        naiveCotangentS'ToF := sorry


/-- Presentation morphism from the `O_{B'}`-polynomial presentation to the thickening
`sol.proj`. -/
def frontPresentationHom (sol : Solution π hπ fSharp G c) :
    Presentation.Hom (FreeAlgebra.base O_B' (generatorSheaf E α sol)) (evalToO E α sol)
      (𝟙 sol.middle) sol.proj where
  base := sol.structureMap
  middle := evalToMiddle E α sol
  target := 𝟙 O
  baseSq := ⟨sorry⟩
  targetSq := ⟨sorry⟩

/-- Front restriction `φ|_{I'} : I'/I'² ⟶ Ker(sol.proj)/Ker(sol.proj)²`. -/
def translateFrontConormal (sol : Solution π hπ fSharp G c) :
    (generatorCotangentS' E α sol).X (-1) ⟶ conormalSource sol.proj :=
  ((extendComplexIdIso O).inv.app (generatorCotangentS' E α sol) ≫
    Presentation.Hom.map (frontPresentationHom E α sol)).f (-1)

/-- Front restriction `φ|_{I'}` as an `O`-linear map `I'/I'² ⟶ 𝒢`. -/
def translateFrontKerModule (sol : Solution π hπ fSharp G c) :
    (generatorCotangentS' E α sol).X (-1) ⟶ G :=
  translateFrontConormal E α sol ≫
    @SquareZeroExtension.conormalToTarget _ _ _ _ _ _ _ _ _ _ _ sol.proj
      sol.proj_locallySurjective sol.proj_squareZero ≫
      sol.kernelIso.hom

/-- The conormal class of a polynomial kernel section in `I'/I'²`. -/
def conormalClass (sol : Solution π hπ fSharp G c) (U : Cᵒᵖ)
    (j : (freeAlgebraS' E α sol).obj.obj U)
    (hj : (evalToO E α sol).hom.app U j = 0) :
    ((generatorCotangentS' E α sol).X (-1)).val.obj U :=
  (conormalSourcePresheafUnit (evalToO E α sol)).app U
    ((conormalIdeal (evalToO E α sol) U).toCotangent ⟨j, hj⟩)

/-- Presentation morphism from the enlarged `O_{B'}`-presentation to the polynomial
presentation of `fSharp`. -/
def enlargedPresentationHom (sol : Solution π hπ fSharp G c) :
    Presentation.Hom (FreeAlgebra.base O_B' (generatorSheaf E α sol)) (evalToO E α sol)
      (FreeAlgebra.base O_B E)
      (FreeAlgebra.evaluation (Under.mk fSharp) E α).right where
  base := π
  middle :=
    (FreeAlgebra.evaluation (Under.mk (π ≫ FreeAlgebra.base O_B E))
      (generatorSheaf E α sol)
      (Limits.pullback.fst α ((sheafForget J).map sol.proj) ≫
        FreeAlgebra.generator O_B E)).right
  target := 𝟙 O
  baseSq := ⟨sorry⟩
  targetSq := ⟨sorry⟩

/-- The comparison `I'/I'² ⟶ I/I²` of the enlarged presentation with the polynomial
conormal source. -/
def translateConormalComparison (sol : Solution π hπ fSharp G c) :
    (generatorCotangentS' E α sol).X (-1) ⟶ (Presentation.ofGenerators E α).X (-1) :=
  ((extendComplexIdIso O).inv.app (generatorCotangentS' E α sol) ≫
    Presentation.Hom.map (enlargedPresentationHom E α sol)).f (-1)

/-- `translateConormalComparison` is degree `-1` of the enlarged presentation map. -/
theorem translateConormalComparison_spec (sol : Solution π hπ fSharp G c) :
    translateConormalComparison E α sol =
      ((extendComplexIdIso O).inv.app (generatorCotangentS' E α sol) ≫
        Presentation.Hom.map (enlargedPresentationHom E α sol)).f (-1) := sorry

variable (δ : (Presentation.ofGenerators E α).X (-1) ⟶ G)

/-- The concrete representative of δ on the enlarged conormal, obtained by composing
the polynomial map `δ : I/I² ⟶ 𝒢` with `I'/I'² ⟶ I/I²`. -/
def translateDelta (sol : Solution π hπ fSharp G c) :
    (generatorCotangentS' E α sol).X (-1) ⟶ G :=
  translateConormalComparison E α sol ≫ δ

/-- `translateDelta` is the polynomial conormal map pulled back along `E ↦ E ×_O O'`. -/
theorem translateDelta_spec (sol : Solution π hπ fSharp G c) :
    translateDelta E α δ sol = translateConormalComparison E α sol ≫ δ := sorry

/-- The `O_{B'}[ℰ](U)`-action on sections of `𝒢` by restriction along `evalToO`. -/
@[reducible] private def moduleFreeAlgebra (sol : Solution π hπ fSharp G c) (U : Cᵒᵖ) :
    Module ((freeAlgebraS' E α sol).obj.obj U) (G.val.obj U) :=
  Module.compHom (G.val.obj U) ((evalToO E α sol).hom.app U).hom

/-- Opposite evaluation of `O_{B'}[ℰ]` on sections, sending rᵒᵖ to the image of r in `O`. -/
def evalToOOp (sol : Solution π hπ fSharp G c) (U : Cᵒᵖ) :
    ((freeAlgebraS' E α sol).obj.obj U)ᵐᵒᵖ →+* O.obj.obj U where
  toFun r := (evalToO E α sol).hom.app U (MulOpposite.unop r)
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry

/-- Opposite `O_{B'}[ℰ](U)`-action on sections of `𝒢`. -/
@[reducible] private def moduleFreeAlgebraOp (sol : Solution π hπ fSharp G c) (U : Cᵒᵖ) :
    Module ((freeAlgebraS' E α sol).obj.obj U)ᵐᵒᵖ (G.val.obj U) :=
  Module.compHom (G.val.obj U) (evalToOOp E α sol U)

/-- The two `O_{B'}[ℰ](U)`-actions on sections of `𝒢` are central. -/
private theorem isCentralScalarFreeAlgebra (sol : Solution π hπ fSharp G c) (U : Cᵒᵖ) :
    -- Local instance justification (instance diamond): TrivSqZeroExt needs the presentation module structures keyed by evaluation O_{B'}[ℰ] ⟶ O.
    letI : Module ((freeAlgebraS' E α sol).obj.obj U) (G.val.obj U) := moduleFreeAlgebra E α sol U
    -- Local instance justification (instance diamond): TrivSqZeroExt needs the opposite presentation module structures keyed by evaluation O_{B'}[ℰ] ⟶ O.
    letI : Module ((freeAlgebraS' E α sol).obj.obj U)ᵐᵒᵖ (G.val.obj U) := moduleFreeAlgebraOp E α sol U
    IsCentralScalar ((freeAlgebraS' E α sol).obj.obj U) (G.val.obj U) :=
  -- Local instance justification (instance diamond): TrivSqZeroExt needs the presentation module structures keyed by evaluation O_{B'}[ℰ] ⟶ O.
  letI : Module ((freeAlgebraS' E α sol).obj.obj U) (G.val.obj U) := moduleFreeAlgebra E α sol U
  -- Local instance justification (instance diamond): TrivSqZeroExt needs the opposite presentation module structures keyed by evaluation O_{B'}[ℰ] ⟶ O.
  letI : Module ((freeAlgebraS' E α sol).obj.obj U)ᵐᵒᵖ (G.val.obj U) := moduleFreeAlgebraOp E α sol U
  ⟨fun _r _n ↦ sorry⟩

/-- The trivial square-zero extension of `O_{B'}[ℰ]` by `𝒢` on sections over `U`. -/
@[no_expose] def translateSectionTriv (sol : Solution π hπ fSharp G c) (U : Cᵒᵖ) : CommRingCat.{w} :=
  -- Local instance justification (instance diamond): TrivSqZeroExt needs the presentation module structures keyed by evaluation O_{B'}[ℰ] ⟶ O.
  letI : Module ((freeAlgebraS' E α sol).obj.obj U) (G.val.obj U) := moduleFreeAlgebra E α sol U
  -- Local instance justification (instance diamond): TrivSqZeroExt needs the opposite presentation module structures keyed by evaluation O_{B'}[ℰ] ⟶ O.
  letI : Module ((freeAlgebraS' E α sol).obj.obj U)ᵐᵒᵖ (G.val.obj U) := moduleFreeAlgebraOp E α sol U
  -- Local instance justification (instance diamond): TrivSqZeroExt.commRing needs centrality of the presentation actions.
  letI : IsCentralScalar ((freeAlgebraS' E α sol).obj.obj U) (G.val.obj U) :=
    isCentralScalarFreeAlgebra E α sol U
  CommRingCat.of (TrivSqZeroExt ((freeAlgebraS' E α sol).obj.obj U) (G.val.obj U))

/-- The first projection of `O_{B'}[ℰ] ⊕ 𝒢` as a ring homomorphism. -/
@[no_expose] def translateFstRingHom (sol : Solution π hπ fSharp G c) (U : Cᵒᵖ) :
    translateSectionTriv E α sol U →+* (freeAlgebraS' E α sol).obj.obj U :=
  -- Local instance justification (instance diamond): TrivSqZeroExt needs the presentation module structures keyed by evaluation O_{B'}[ℰ] ⟶ O.
  letI : Module ((freeAlgebraS' E α sol).obj.obj U) (G.val.obj U) := moduleFreeAlgebra E α sol U
  -- Local instance justification (instance diamond): TrivSqZeroExt needs the opposite presentation module structures keyed by evaluation O_{B'}[ℰ] ⟶ O.
  letI : Module ((freeAlgebraS' E α sol).obj.obj U)ᵐᵒᵖ (G.val.obj U) := moduleFreeAlgebraOp E α sol U
  -- Local instance justification (instance diamond): TrivSqZeroExt.commRing needs centrality of the presentation actions.
  letI : IsCentralScalar ((freeAlgebraS' E α sol).obj.obj U) (G.val.obj U) :=
    isCentralScalarFreeAlgebra E α sol U
  { toFun := TrivSqZeroExt.fst
    map_one' := TrivSqZeroExt.fst_one
    map_mul' := TrivSqZeroExt.fst_mul
    map_zero' := TrivSqZeroExt.fst_zero
    map_add' := TrivSqZeroExt.fst_add }

/-- Front restriction `φ|_{I'}` on a polynomial kernel section, as the image of
`evalToMiddle j` under `sol.kernelIso`. -/
def translateFrontKerMap (sol : Solution π hπ fSharp G c) (U : Cᵒᵖ)
    (j : (freeAlgebraS' E α sol).obj.obj U)
    (hj : (evalToO E α sol).hom.app U j = 0) : G.val.obj U :=
  (translateFrontKerModule E α sol).val.app U (conormalClass E α sol U j hj)

/-- The map `ψ = φ|_{I'} + δ` on a polynomial kernel section. -/
def translateKerMap
    (sol : Solution π hπ fSharp G c) (U : Cᵒᵖ)
    (j : (freeAlgebraS' E α sol).obj.obj U)
    (hj : (evalToO E α sol).hom.app U j = 0) : G.val.obj U :=
  translateFrontKerMap E α sol U j hj +
    (translateDelta E α δ sol).val.app U (conormalClass E α sol U j hj)

/-- `translateKerMap` adds the front kernel restriction to the polynomial conormal map δ. -/
theorem translateKerMap_spec
    (sol : Solution π hπ fSharp G c) (U : Cᵒᵖ)
    (j : (freeAlgebraS' E α sol).obj.obj U)
    (hj : (evalToO E α sol).hom.app U j = 0) :
    translateKerMap E α δ sol U j hj =
      translateFrontKerMap E α sol U j hj +
        (translateDelta E α δ sol).val.app U (conormalClass E α sol U j hj) := sorry

/-- The graph ideal of `ψ` in the trivial square-zero extension `O_{B'}[ℰ] ⊕ 𝒢`. -/
@[no_expose] def translateGraphIdeal
    (sol : Solution π hπ fSharp G c) (U : Cᵒᵖ) :
    Ideal (translateSectionTriv E α sol U) :=
  -- Local instance justification (instance diamond): TrivSqZeroExt needs the presentation module structures keyed by evaluation O_{B'}[ℰ] ⟶ O.
  letI : Module ((freeAlgebraS' E α sol).obj.obj U) (G.val.obj U) := moduleFreeAlgebra E α sol U
  -- Local instance justification (instance diamond): TrivSqZeroExt needs the opposite presentation module structures keyed by evaluation O_{B'}[ℰ] ⟶ O.
  letI : Module ((freeAlgebraS' E α sol).obj.obj U)ᵐᵒᵖ (G.val.obj U) := moduleFreeAlgebraOp E α sol U
  -- Local instance justification (instance diamond): TrivSqZeroExt.commRing needs centrality of the presentation actions.
  letI : IsCentralScalar ((freeAlgebraS' E α sol).obj.obj U) (G.val.obj U) :=
    isCentralScalarFreeAlgebra E α sol U
  Ideal.span <| Set.range fun j : RingHom.ker ((evalToO E α sol).hom.app U).hom ↦
    TrivSqZeroExt.inl (R := (freeAlgebraS' E α sol).obj.obj U) (M := G.val.obj U) j.1 -
      TrivSqZeroExt.inr (translateKerMap E α δ sol U j.1 j.2)

/-- The section ring of the pushout `O'_ξ` over `U`. -/
def translateSectionRing
    (sol : Solution π hπ fSharp G c) (U : Cᵒᵖ) : CommRingCat.{w} :=
  CommRingCat.of (translateSectionTriv E α sol U ⧸ translateGraphIdeal E α δ sol U)

/-- Restriction of a section of `O_{B'}[ℰ] ⊕ 𝒢` along a morphism of the site. -/
@[no_expose] def translateTrivRestriction (sol : Solution π hπ fSharp G c) {U V : Cᵒᵖ} (rho : U ⟶ V) :
    translateSectionTriv E α sol U ⟶ translateSectionTriv E α sol V :=
  -- Local instance justification (instance diamond): TrivSqZeroExt needs the presentation module structures keyed by evaluation O_{B'}[ℰ] ⟶ O.
  letI : Module ((freeAlgebraS' E α sol).obj.obj U) (G.val.obj U) := moduleFreeAlgebra E α sol U
  -- Local instance justification (instance diamond): TrivSqZeroExt needs the opposite presentation module structures keyed by evaluation O_{B'}[ℰ] ⟶ O.
  letI : Module ((freeAlgebraS' E α sol).obj.obj U)ᵐᵒᵖ (G.val.obj U) := moduleFreeAlgebraOp E α sol U
  -- Local instance justification (instance diamond): TrivSqZeroExt.commRing needs centrality of the presentation actions.
  letI : IsCentralScalar ((freeAlgebraS' E α sol).obj.obj U) (G.val.obj U) :=
    isCentralScalarFreeAlgebra E α sol U
  -- Local instance justification (instance diamond): TrivSqZeroExt needs the presentation module structures keyed by evaluation O_{B'}[ℰ] ⟶ O.
  letI : Module ((freeAlgebraS' E α sol).obj.obj V) (G.val.obj V) := moduleFreeAlgebra E α sol V
  -- Local instance justification (instance diamond): TrivSqZeroExt needs the opposite presentation module structures keyed by evaluation O_{B'}[ℰ] ⟶ O.
  letI : Module ((freeAlgebraS' E α sol).obj.obj V)ᵐᵒᵖ (G.val.obj V) := moduleFreeAlgebraOp E α sol V
  -- Local instance justification (instance diamond): TrivSqZeroExt.commRing needs centrality of the presentation actions.
  letI : IsCentralScalar ((freeAlgebraS' E α sol).obj.obj V) (G.val.obj V) :=
    isCentralScalarFreeAlgebra E α sol V
  CommRingCat.ofHom
    { toFun := fun x ↦
        (((freeAlgebraS' E α sol).obj.map rho (TrivSqZeroExt.fst x),
            G.val.map rho (TrivSqZeroExt.snd x)) :
          TrivSqZeroExt ((freeAlgebraS' E α sol).obj.obj V) (G.val.obj V))
      map_zero' := sorry
      map_one' := sorry
      map_add' := sorry
      map_mul' := sorry }

/-- Restriction of the pushout section ring along a morphism of the site. -/
def translateRestriction
    (sol : Solution π hπ fSharp G c) {U V : Cᵒᵖ} (rho : U ⟶ V) :
    translateSectionRing E α δ sol U ⟶ translateSectionRing E α δ sol V :=
  CommRingCat.ofHom
    (Ideal.Quotient.lift (translateGraphIdeal E α δ sol U)
      ((Ideal.Quotient.mk (translateGraphIdeal E α δ sol V)).comp
        (translateTrivRestriction E α sol rho).hom) sorry)

/-- The presheaf of pushout rings `O'_ξ`. -/
def translatePresheaf
    (sol : Solution π hπ fSharp G c) : Cᵒᵖ ⥤ CommRingCat.{w} where
  obj U := translateSectionRing E α δ sol U
  map rho := translateRestriction E α δ sol rho
  map_id U := sorry
  map_comp rho sigma := sorry

/-- The pushout algebra is the sheafification of the graph-quotient presheaf. -/
def translateSheaf (sol : Solution π hπ fSharp G c) : Sheaf J CommRingCat.{w} :=
  (presheafToSheaf J CommRingCat.{w}).obj (translatePresheaf E α δ sol)

/-- Sheafification supplies the sheaf condition, without asserting it for the raw quotient. -/
theorem translateSheaf_isSheaf (sol : Solution π hπ fSharp G c) :
    Presheaf.IsSheaf J (translateSheaf E α δ sol).obj :=
  (translateSheaf E α δ sol).property

/-- The structure-sheaf map `O'_ξ ⟶ O` of the translated thickening. -/
def translateProj
    (sol : Solution π hπ fSharp G c) :
    translateSheaf E α δ sol ⟶ O :=
  ((sheafificationAdjunction J CommRingCat.{w}).homEquiv (translatePresheaf E α δ sol) O).symm
    { app U :=
        CommRingCat.ofHom
          (Ideal.Quotient.lift (translateGraphIdeal E α δ sol U)
            (((evalToO E α sol).hom.app U).hom.comp (translateFstRingHom E α sol U)) sorry)
      naturality {_ _} rho := sorry }

variable [hEval : IsLocallySurjective (FreeAlgebra.evaluation (Under.mk fSharp) E α).right]

/-- The translated projection `O'_ξ ⟶ O` is locally surjective. -/
theorem instIsLocallySurjective_translateProj
    (sol : Solution π hπ fSharp G c) :
    Sheaf.IsLocallySurjective (translateProj E α δ sol) := sorry

/-- The translated projection `O'_ξ ⟶ O` is square-zero. -/
theorem translateProj_squareZero
    (sol : Solution π hπ fSharp G c) :
    KernelIdeal.IsSquareZero (translateProj E α δ sol) := sorry

/-- The structure-sheaf map `O_{B'} ⟶ O'_ξ` of a translated solution. -/
@[no_expose] def translateStructureMap
    (sol : Solution π hπ fSharp G c) :
    O_B' ⟶ translateSheaf E α δ sol :=
  ObjectProperty.homMk
    ({ app U :=
        CommRingCat.ofHom
          ((Ideal.Quotient.mk (translateGraphIdeal E α δ sol U)).comp
            ((
              -- Local instance justification (instance diamond): TrivSqZeroExt needs the presentation module structures keyed by evaluation O_{B'}[ℰ] ⟶ O.
              letI : Module ((freeAlgebraS' E α sol).obj.obj U) (G.val.obj U) :=
                moduleFreeAlgebra E α sol U
              -- Local instance justification (instance diamond): TrivSqZeroExt needs the opposite presentation module structures keyed by evaluation O_{B'}[ℰ] ⟶ O.
              letI : Module ((freeAlgebraS' E α sol).obj.obj U)ᵐᵒᵖ (G.val.obj U) :=
                moduleFreeAlgebraOp E α sol U
              -- Local instance justification (instance diamond): TrivSqZeroExt.commRing needs centrality of the presentation actions.
              letI : IsCentralScalar ((freeAlgebraS' E α sol).obj.obj U) (G.val.obj U) :=
                isCentralScalarFreeAlgebra E α sol U
              TrivSqZeroExt.inlHom ((freeAlgebraS' E α sol).obj.obj U) (G.val.obj U)).comp
              ((FreeAlgebra.base O_B' (generatorSheaf E α sol)).hom.app U).hom))
       naturality {_ _} rho := sorry } ≫ toSheafify J (translatePresheaf E α δ sol))

/-- The fixed inclusion sends n to the sheafification of the quotient class of (0,n). -/
@[no_expose] def translateKernelInclusion (sol : Solution π hπ fSharp G c) :
    G ⟶ (translateProj_squareZero E α δ sol).targetModule
      (@KernelIdeal.quotientComparison_isIso _ _ _ _ _ _ _
        (translateProj E α δ sol) _ (instIsLocallySurjective_translateProj E α δ sol)) :=
    { val :=
        PresheafOfModules.homMk
          { app U :=
              AddCommGrpCat.ofHom <|
                AddMonoidHom.mk'
                  (fun n ↦
                    -- Local instance justification (instance diamond): TrivSqZeroExt needs the presentation module structures keyed by evaluation O_{B'}[ℰ] ⟶ O.
                    letI : Module ((freeAlgebraS' E α sol).obj.obj U) (G.val.obj U) :=
                      moduleFreeAlgebra E α sol U
                    -- Local instance justification (instance diamond): TrivSqZeroExt needs the opposite presentation module structures keyed by evaluation O_{B'}[ℰ] ⟶ O.
                    letI : Module ((freeAlgebraS' E α sol).obj.obj U)ᵐᵒᵖ (G.val.obj U) :=
                      moduleFreeAlgebraOp E α sol U
                    -- Local instance justification (instance diamond): TrivSqZeroExt.commRing needs centrality of the presentation actions.
                    letI : IsCentralScalar ((freeAlgebraS' E α sol).obj.obj U) (G.val.obj U) :=
                      isCentralScalarFreeAlgebra E α sol U
                    let raw :=
                      Ideal.Quotient.mk (translateGraphIdeal E α δ sol U) (TrivSqZeroExt.inr n)
                    let z := (toSheafify J (translatePresheaf E α δ sol)).app U raw
                    ((translateProj_squareZero E α δ sol).targetModuleForgetIso
                          (@KernelIdeal.quotientComparison_isIso _ _ _ _ _ _ _
                            (translateProj E α δ sol) _
                            (instIsLocallySurjective_translateProj E α δ sol))).inv.hom.app
                      U ((KernelIdeal.sectionsIso (translateProj E α δ sol) U).inv ⟨z, sorry⟩))
                  sorry
            naturality {_ _} _ := sorry }
          (fun _ _ _ ↦ sorry) }

/-- The locally surjective presentation makes this coefficient inclusion invertible. -/
theorem translateKernelInclusion_isIso (sol : Solution π hπ fSharp G c) :
    IsIso (translateKernelInclusion E α δ sol) := sorry

/-- Invert the specified coefficient inclusion; no global section lift is selected. -/
def translateKernelIsoOf (sol : Solution π hπ fSharp G c)
    (hk : IsIso (translateKernelInclusion E α δ sol)) :
    (translateProj_squareZero E α δ sol).targetModule
      (@KernelIdeal.quotientComparison_isIso _ _ _ _ _ _ _
        (translateProj E α δ sol) _ (instIsLocallySurjective_translateProj E α δ sol)) ≅ G :=
  (@asIso _ _ _ _ (translateKernelInclusion E α δ sol) hk).symm

/-- Choice-free constructor: the pushout of `O_{B'}[E ×_O O']` along `ψ = φ|_{I'} + δ`
for an explicit polynomial conormal representative `δ`. -/
def translateOfWith (sol : Solution π hπ fSharp G c)
    (hk : IsIso (translateKernelInclusion E α δ sol)) :
    Solution π hπ fSharp G c where
  middle := translateSheaf E α δ sol
  proj := translateProj E α δ sol
  structureMap := translateStructureMap E α δ sol
  proj_locallySurjective := instIsLocallySurjective_translateProj E α δ sol
  proj_squareZero := translateProj_squareZero E α δ sol
  proj_quotient_isIso := @KernelIdeal.quotientComparison_isIso _ _ _ _ _ _ _
    (translateProj E α δ sol) _ (instIsLocallySurjective_translateProj E α δ sol)
  commutes := sorry
  kernelIso := translateKernelIsoOf E α δ sol hk
  induces_c := sorry

/-- The translate of a solution along an explicit conormal map is again a solution of
the fixed extension diagram, with structure sheaf the pushout of `O_{B'}[E ×_O O']` along `ψ`. -/
theorem translateOfWith_spec (sol : Solution π hπ fSharp G c)
    (hk : IsIso (translateKernelInclusion E α δ sol)) :
    (translateOfWith E α δ sol hk).middle = translateSheaf E α δ sol ∧
      (translateOfWith E α δ sol hk).proj = translateProj E α δ sol ∧
        (translateOfWith E α δ sol hk).structureMap = translateStructureMap E α δ sol := sorry

end Of

/-- A conormal representative of an extension class, with certificates for its specified maps. -/
structure TranslationData
    (ξ : Ext⁽(1 : ℤ)⁾(DerivedCategory.Q.obj (NaiveCotangent.obj O_B (Under.mk fSharp)),
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj G))) where
  /-- The sheaf of polynomial generators. -/
  E : Sheaf J (Type w)
  /-- Their specified values in the target ring sheaf. -/
  α : E ⟶ FreeAlgebra.Presentation.generators (Under.mk fSharp)
  /-- The associated evaluation is locally surjective. -/
  evaluation : IsLocallySurjective (FreeAlgebra.evaluation (Under.mk fSharp) E α).right
  /-- The conormal map representing the extension class. -/
  δ : (Presentation.ofGenerators E α).X (-1) ⟶ G
  /-- The canonical comparison is a quasi-isomorphism. -/
  hq : QuasiIso (Presentation.toCanonicalMap E α)
  /-- The conormal map represents the specified extension class. -/
  represents : Presentation.derivedComparison E α ≫ ξ = conormalHomClass fSharp G E α δ
  /-- The graph quotient identifies its kernel with the coefficient module. -/
  kernelIsIso : ∀ sol : Solution π hπ fSharp G c,
    IsIso (translateKernelInclusion E α δ sol (hEval := evaluation))

/-- Translate a solution using a supplied conormal representative and kernel certificate. -/
def translateWith
    {ξ : Ext⁽(1 : ℤ)⁾(DerivedCategory.Q.obj (NaiveCotangent.obj O_B (Under.mk fSharp)),
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj G))}
    (d : TranslationData (π := π) (hπ := hπ) (c := c) ξ)
    (sol : Solution π hπ fSharp G c) : Solution π hπ fSharp G c :=
  translateOfWith d.E d.α d.δ sol (d.kernelIsIso sol) (hEval := d.evaluation)

/-- A solution is a translation when it is the graph quotient of an actual representative. -/
def IsTranslation
    (ξ : Ext⁽(1 : ℤ)⁾(DerivedCategory.Q.obj (NaiveCotangent.obj O_B (Under.mk fSharp)),
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj G)))
    (S T : Solution π hπ fSharp G c) : Prop :=
  ∃ d : TranslationData (π := π) (hπ := hπ) (c := c) ξ, T = translateWith d S

end Solution
end SheafOfModules.RingedSite.FirstOrderThickening
