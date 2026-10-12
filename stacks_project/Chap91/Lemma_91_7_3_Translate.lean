/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import stacks_project.Chap91.Lemma_91_7_1_Obstruction
public import stacks_project.Chap91.Lemma_91_7_2
public import stacks_project.Chap91.«91_4_5_1_SquareZero»

/-!
# Pushout translate of a first-order ringed-space solution

Given a solution of 91.7.0.1 and a class ξ in Ext⁽1⁾(Q NL[f], Q(𝒢[0])), the
source constructs a second solution X'_ξ as the sheaf-of-rings pushout of
f⁻¹𝒪_{S'}[ℰ] along ψ = φ|_{I'} + δ. Here (E, α, δ) is a 91.7.2 conormal
representative of ξ for a presentation of 𝒪_X over f⁻¹𝒪_S, the sheaf ℰ is
E ×_{𝒪_X} i⁻¹𝒪_{X'}, and δ is transported along I'/I'² ⟶ I/I².
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf
open AlgebraicGeometry
open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.RingedSpace.Hom
open AlgebraicGeometry.RingedSpace.Thickening
open SheafOfModules.RingedSite
open SheafOfModules.RingedSite.NaiveCotangent
open HomologicalComplex DerivedCategory
open Opposite TopologicalSpace TrivSqZeroExt
open scoped AlgebraicGeometry DerivedExt RingedSpaceDerivedPullback
open scoped CategoryTheory.Sheaf.FreeAlgebra

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Thickening
namespace Solution

variable {S S' X : RingedSpace.{u}} {t : S ⟶ S'} [IsFirstOrderThickening t] {f : X ⟶ S}
variable {G : X.Modules} {c : Hom.idealModule t ⟶ (f _*).obj G}

/-- A solution supplies a first-order thickening `i : X ⟶ X'`. -/
instance instIsFirstOrderThickening_i (sol : Solution t f G c) :
    IsFirstOrderThickening sol.i :=
  sol.i_isFirstOrder

/-- Inverse image of `𝒪_{X'}` along the thickening of a solution. -/
def inverseImageX' (sol : Solution t f G c) :
    Sheaf (Opens.grothendieckTopology X) CommRingCat.{u} :=
  (TopCat.Sheaf.pullback CommRingCat.{u} sol.i.hom.base).obj sol.space.sheaf

/-- Inverse image of `𝒪_{S'}` along `sol.i ≫ sol.f'`. -/
def inverseImageS' (sol : Solution t f G c) :
    Sheaf (Opens.grothendieckTopology X) CommRingCat.{u} :=
  (TopCat.Sheaf.pullback CommRingCat.{u} (sol.i ≫ sol.f').hom.base).obj S'.sheaf

/-- The structure map `(sol.i ≫ sol.f')⁻¹ 𝒪_{S'} ⟶ sol.i⁻¹ 𝒪_{X'}`. -/
def inverseImageS'ToX' (sol : Solution t f G c) :
    inverseImageS' sol ⟶ inverseImageX' sol :=
  (Hom.StructureSheaf.compIso sol.i sol.f').inv ≫
    (TopCat.Sheaf.pullback CommRingCat.{u} sol.i.hom.base).map
      (inverseImageStructureSheafHomComm sol.f')

/-- The structure map `(sol.i ≫ sol.f')⁻¹ 𝒪_{S'} ⟶ 𝒪_X`. -/
def inverseImageS'ToX (sol : Solution t f G c) :
    inverseImageS' sol ⟶ X.sheaf :=
  inverseImageS'ToX' sol ≫ inverseImageStructureSheafHomComm sol.i

/-- Inverse image of `𝒪_{S'}` along `sol.i ≫ sol.f'` is the inverse image along `f ≫ t`. -/
def inverseImageS'IsoComposite (sol : Solution t f G c) :
    inverseImageS' sol ≅
      (TopCat.Sheaf.pullback CommRingCat.{u} (f ≫ t).hom.base).obj S'.sheaf :=
  (TopCat.Sheaf.pullbackCongr (A := CommRingCat.{u})
    (congrArg (fun k : X ⟶ S' ↦ k.hom.base) sol.commutes)).app S'.sheaf

/-- The coefficient map `(sol.i ≫ sol.f')⁻¹ 𝒪_{S'} ⟶ f⁻¹ 𝒪_S`. -/
def inverseImageS'ToS (sol : Solution t f G c) :
    inverseImageS' sol ⟶
      (TopCat.Sheaf.pullback CommRingCat.{u} f.hom.base).obj S.sheaf :=
  (inverseImageS'IsoComposite sol).hom ≫ transportedT1Sharp f t

/-- `inverseImageS'ToS` is source change along `sol.commutes` followed by the inverse image of
`t^♯`. -/
theorem inverseImageS'ToS_spec (sol : Solution t f G c) :
    inverseImageS'ToS sol = (inverseImageS'IsoComposite sol).hom ≫ transportedT1Sharp f t :=
  sorry

section Of

variable (E : Sheaf (Opens.grothendieckTopology X) (Type u))
variable (α : E ⟶ FreeAlgebra.Presentation.generators (inverseImageStructureSheafUnder f))

/-- The fiber-product sheaf of sets `E ×_{𝒪_X} i⁻¹ 𝒪_{X'}`. -/
def generatorSheaf (sol : Solution t f G c) :
    Sheaf (Opens.grothendieckTopology X) (Type u) :=
  pullback α ((sheafForget (Opens.grothendieckTopology X)).map
    (inverseImageStructureSheafHomComm sol.i))

/-- `generatorSheaf` is the pullback of the 91.7.2 generators along `sol.i^♯`. -/
theorem generatorSheaf_spec (sol : Solution t f G c) :
    generatorSheaf E α sol =
      pullback α ((sheafForget (Opens.grothendieckTopology X)).map
        (inverseImageStructureSheafHomComm sol.i)) := sorry

/-- Assignment of fiber-product generators to `𝒪_X`. -/
def generatorAssign (sol : Solution t f G c) :
    generatorSheaf E α sol ⟶
      FreeAlgebra.Presentation.generators (inverseImageStructureSheafUnder f) :=
  pullback.fst α ((sheafForget (Opens.grothendieckTopology X)).map
    (inverseImageStructureSheafHomComm sol.i)) ≫ α

/-- Assignment of fiber-product generators to `sol.i⁻¹ 𝒪_{X'}`. -/
def generatorFrontAssign (sol : Solution t f G c) :
    generatorSheaf E α sol ⟶
      (sheafForget (Opens.grothendieckTopology X)).obj (inverseImageX' sol) :=
  pullback.snd α ((sheafForget (Opens.grothendieckTopology X)).map
    (inverseImageStructureSheafHomComm sol.i))

/-- The polynomial algebra `f⁻¹ 𝒪_{S'}[ℰ]`. -/
def freeAlgebraS' (sol : Solution t f G c) :
    Sheaf (Opens.grothendieckTopology X) CommRingCat.{u} :=
  (inverseImageS' sol) [generatorSheaf E α sol]

/-- Evaluation `φ : f⁻¹ 𝒪_{S'}[ℰ] ⟶ sol.i⁻¹ 𝒪_{X'}` on fiber-product generators. -/
def evalToX' (sol : Solution t f G c) :
    freeAlgebraS' E α sol ⟶ inverseImageX' sol :=
  (FreeAlgebra.evaluation (Under.mk (inverseImageS'ToX' sol))
    (generatorSheaf E α sol) (generatorFrontAssign E α sol)).right

/-- Evaluation `f⁻¹ 𝒪_{S'}[ℰ] ⟶ 𝒪_X` on fiber-product generators. -/
def evalToX (sol : Solution t f G c) :
    freeAlgebraS' E α sol ⟶ X.sheaf :=
  (FreeAlgebra.evaluation (Under.mk (inverseImageS'ToX sol))
    (generatorSheaf E α sol) (generatorAssign E α sol)).right

/-- `evalToX` is free-algebra evaluation of the fiber-product generators on `𝒪_X`. -/
theorem evalToX_spec (sol : Solution t f G c) :
    evalToX E α sol =
      (FreeAlgebra.evaluation (Under.mk (inverseImageS'ToX sol))
        (generatorSheaf E α sol) (generatorAssign E α sol)).right := sorry

/-- `evalToX'` is free-algebra evaluation of the fiber-product generators on `sol.i⁻¹ 𝒪_{X'}`. -/
theorem evalToX'_spec (sol : Solution t f G c) :
    evalToX' E α sol =
      (FreeAlgebra.evaluation (Under.mk (inverseImageS'ToX' sol))
        (generatorSheaf E α sol) (generatorFrontAssign E α sol)).right := sorry

/-- The `𝒪_{S'}`-polynomial presentation of `𝒪_X` on the fiber-product generators. -/
def generatorCotangentS' (sol : Solution t f G c) : CochainComplex X.Modules ℤ :=
  Presentation.ofGenerators (B := Under.mk (inverseImageS'ToX sol))
    (generatorSheaf E α sol) (generatorAssign E α sol)

/-- Presentation morphism from the `𝒪_{S'}`-polynomial presentation to the thickening
`sol.i`. -/
def frontPresentationHom (sol : Solution t f G c) :
    Presentation.Hom
      (FreeAlgebra.base (inverseImageS' sol) (generatorSheaf E α sol))
      (evalToX E α sol)
      (𝟙 (inverseImageX' sol))
      (inverseImageStructureSheafHomComm sol.i) where
  base := inverseImageS'ToX' sol
  middle := evalToX' E α sol
  target := 𝟙 _
  baseSq := sorry
  targetSq := sorry

/-- Front restriction `φ|_{I'} : I'/I'² ⟶ Ker(sol.i^♯)/Ker(sol.i^♯)²`. -/
def translateFrontConormal (sol : Solution t f G c) :
    (generatorCotangentS' E α sol).X (-1) ⟶ Hom.conormalSheaf sol.i :=
  ((extendComplexIdIso X.sheaf).inv.app (generatorCotangentS' E α sol) ≫
    Presentation.Hom.map (frontPresentationHom E α sol)).f (-1)

/-- Front restriction `φ|_{I'}` as an `𝒪_X`-linear map `I'/I'² ⟶ 𝒢`. -/
def translateFrontKerModule (sol : Solution t f G c) :
    (generatorCotangentS' E α sol).X (-1) ⟶ G :=
  translateFrontConormal E α sol ≫
    conormalToTargetModule sol.i ≫
      targetModuleToIdealModule sol.i ≫ sol.kernelIso.hom

/-- The conormal class of a polynomial kernel section in `I'/I'²`. -/
def conormalClass (sol : Solution t f G c) (U : (Opens X)ᵒᵖ)
    (j : (freeAlgebraS' E α sol).obj.obj U)
    (hj : (evalToX E α sol).hom.app U j = 0) :
    ((generatorCotangentS' E α sol).X (-1)).val.obj U :=
  (conormalSourcePresheafUnit (evalToX E α sol)).app U
    ((conormalIdeal (evalToX E α sol) U).toCotangent ⟨j, hj⟩)

/-- Presentation morphism from the enlarged `𝒪_{S'}`-presentation to the 91.7.2 presentation
of `𝒪_X` over `f⁻¹ 𝒪_S`. -/
def enlargedPresentationHom (sol : Solution t f G c) :
    Presentation.Hom
      (FreeAlgebra.base (inverseImageS' sol) (generatorSheaf E α sol))
      (evalToX E α sol)
      (FreeAlgebra.base
        ((TopCat.Sheaf.pullback CommRingCat.{u} f.hom.base).obj S.sheaf) E)
      (FreeAlgebra.evaluation (inverseImageStructureSheafUnder f) E α).right where
  base := inverseImageS'ToS sol
  middle :=
    (FreeAlgebra.evaluation
        (Under.mk
          (inverseImageS'ToS sol ≫
            FreeAlgebra.base
              ((TopCat.Sheaf.pullback CommRingCat.{u} f.hom.base).obj S.sheaf) E))
        (generatorSheaf E α sol)
        (pullback.fst α ((sheafForget (Opens.grothendieckTopology X)).map
            (inverseImageStructureSheafHomComm sol.i)) ≫
          FreeAlgebra.generator
            ((TopCat.Sheaf.pullback CommRingCat.{u} f.hom.base).obj S.sheaf) E)).right
  target := 𝟙 _
  baseSq := sorry
  targetSq := sorry

/-- The comparison `I'/I'² ⟶ I/I²` of the enlarged presentation with the 91.7.2
conormal source. -/
def translateConormalComparison (sol : Solution t f G c) :
    (generatorCotangentS' E α sol).X (-1) ⟶ (Presentation.ofGenerators E α).X (-1) :=
  ((extendComplexIdIso X.sheaf).inv.app (generatorCotangentS' E α sol) ≫
    Presentation.Hom.map (enlargedPresentationHom E α sol)).f (-1)

/-- `translateConormalComparison` is degree `-1` of the enlarged presentation map. -/
theorem translateConormalComparison_spec (sol : Solution t f G c) :
    translateConormalComparison E α sol =
      ((extendComplexIdIso X.sheaf).inv.app (generatorCotangentS' E α sol) ≫
        Presentation.Hom.map (enlargedPresentationHom E α sol)).f (-1) := sorry

variable (δ : (Presentation.ofGenerators E α).X (-1) ⟶ G)

/-- The concrete representative of δ on the enlarged conormal, obtained by composing
the 91.7.2 map `δ : I/I² ⟶ 𝒢` with `I'/I'² ⟶ I/I²`. -/
def translateDelta (sol : Solution t f G c) :
    (generatorCotangentS' E α sol).X (-1) ⟶ G :=
  translateConormalComparison E α sol ≫ δ

/-- `translateDelta` is the 91.7.2 conormal map pulled back along `E ↦ E ×_{𝒪_X} i⁻¹ 𝒪_{X'}`. -/
theorem translateDelta_spec (sol : Solution t f G c) :
    translateDelta E α δ sol = translateConormalComparison E α sol ≫ δ := sorry

/-- The `f⁻¹ 𝒪_{S'}[ℰ](U)`-action on sections of `𝒢` by restriction along `evalToX`. -/
instance instModule_translateSection (sol : Solution t f G c) (U : (Opens X)ᵒᵖ) :
    Module ((freeAlgebraS' E α sol).obj.obj U) (G.val.obj U) :=
  Module.compHom (G.val.obj U) ((evalToX E α sol).hom.app U).hom

/-- The opposite `f⁻¹ 𝒪_{S'}[ℰ](U)`-action on sections of `𝒢`. -/
instance instModuleOp_translateSection (sol : Solution t f G c) (U : (Opens X)ᵒᵖ) :
    Module ((freeAlgebraS' E α sol).obj.obj U)ᵐᵒᵖ (G.val.obj U) :=
  Module.compHom (G.val.obj U)
    (((evalToX E α sol).hom.app U).hom.fromOpposite fun x y ↦
      mul_comm (((evalToX E α sol).hom.app U).hom x) (((evalToX E α sol).hom.app U).hom y))

/-- The two `f⁻¹ 𝒪_{S'}[ℰ](U)`-actions on sections of `𝒢` are central. -/
instance instIsCentralScalar_translateSection (sol : Solution t f G c) (U : (Opens X)ᵒᵖ) :
    IsCentralScalar ((freeAlgebraS' E α sol).obj.obj U) (G.val.obj U) where
  op_smul_eq_smul := sorry

/-- The trivial square-zero extension of `f⁻¹ 𝒪_{S'}[ℰ]` by `𝒢` on sections over `U`. -/
def translateSectionTriv (sol : Solution t f G c) (U : (Opens X)ᵒᵖ) : CommRingCat.{u} :=
  CommRingCat.of (TrivSqZeroExt ((freeAlgebraS' E α sol).obj.obj U) (G.val.obj U))

/-- The first projection of `f⁻¹ 𝒪_{S'}[ℰ] ⊕ 𝒢` as a ring homomorphism. -/
def translateFstRingHom (sol : Solution t f G c) (U : (Opens X)ᵒᵖ) :
    translateSectionTriv E α sol U →+* (freeAlgebraS' E α sol).obj.obj U where
  toFun := TrivSqZeroExt.fst
  map_one' := TrivSqZeroExt.fst_one
  map_mul' := TrivSqZeroExt.fst_mul
  map_zero' := TrivSqZeroExt.fst_zero
  map_add' := TrivSqZeroExt.fst_add

/-- Front restriction `φ|_{I'}` on a polynomial kernel section, as the image of
`evalToX' j` under `sol.kernelIso`. -/
def translateFrontKerMap (sol : Solution t f G c) (U : (Opens X)ᵒᵖ)
    (j : (freeAlgebraS' E α sol).obj.obj U)
    (hj : (evalToX E α sol).hom.app U j = 0) : G.val.obj U :=
  (translateFrontKerModule E α sol).val.app U (conormalClass E α sol U j hj)

/-- Polynomial evaluation in the kernel of `sol.i^♯` is identified with `𝒢` via
`kernelIso` after passage to `I'/I'²`. -/
theorem translateFrontKerMap_spec (sol : Solution t f G c) (U : (Opens X)ᵒᵖ)
    (j : (freeAlgebraS' E α sol).obj.obj U)
    (hj : (evalToX E α sol).hom.app U j = 0) :
    translateFrontKerMap E α sol U j hj =
      (translateFrontKerModule E α sol).val.app U (conormalClass E α sol U j hj) := sorry

/-- The map `ψ = φ|_{I'} + δ` on a polynomial kernel section. -/
def translateKerMap (sol : Solution t f G c) (U : (Opens X)ᵒᵖ)
    (j : (freeAlgebraS' E α sol).obj.obj U)
    (hj : (evalToX E α sol).hom.app U j = 0) : G.val.obj U :=
  translateFrontKerMap E α sol U j hj +
    (translateDelta E α δ sol).val.app U (conormalClass E α sol U j hj)

/-- `translateKerMap` adds the front kernel restriction to the 91.7.2 conormal map δ. -/
theorem translateKerMap_spec (sol : Solution t f G c) (U : (Opens X)ᵒᵖ)
    (j : (freeAlgebraS' E α sol).obj.obj U)
    (hj : (evalToX E α sol).hom.app U j = 0) :
    translateKerMap E α δ sol U j hj =
      translateFrontKerMap E α sol U j hj +
        (translateDelta E α δ sol).val.app U (conormalClass E α sol U j hj) := sorry

/-- The graph ideal of `ψ` in the trivial square-zero extension `f⁻¹ 𝒪_{S'}[ℰ] ⊕ 𝒢`. -/
def translateGraphIdeal (sol : Solution t f G c) (U : (Opens X)ᵒᵖ) :
    Ideal (translateSectionTriv E α sol U) :=
  Ideal.span <| Set.range fun j : RingHom.ker ((evalToX E α sol).hom.app U).hom ↦
    TrivSqZeroExt.inl (R := (freeAlgebraS' E α sol).obj.obj U) (M := G.val.obj U) j.1 -
      TrivSqZeroExt.inr (translateKerMap E α δ sol U j.1 j.2)

/-- The section ring of the pushout `𝒪_{X'_ξ}` over `U`. -/
def translateSectionRing (sol : Solution t f G c) (U : (Opens X)ᵒᵖ) : CommRingCat.{u} :=
  CommRingCat.of (translateSectionTriv E α sol U ⧸ translateGraphIdeal E α δ sol U)

/-- Restriction of a section of `f⁻¹ 𝒪_{S'}[ℰ] ⊕ 𝒢` along a morphism of opens. -/
def translateTrivRestriction (sol : Solution t f G c) {U V : (Opens X)ᵒᵖ} (rho : U ⟶ V) :
    translateSectionTriv E α sol U ⟶ translateSectionTriv E α sol V :=
  CommRingCat.ofHom
    { toFun := fun x ↦
        (((freeAlgebraS' E α sol).obj.map rho (TrivSqZeroExt.fst x),
            G.val.map rho (TrivSqZeroExt.snd x)) :
          TrivSqZeroExt ((freeAlgebraS' E α sol).obj.obj V) (G.val.obj V))
      map_zero' := sorry
      map_one' := sorry
      map_add' := sorry
      map_mul' := sorry }

/-- Restriction of the pushout section ring along a morphism of opens. -/
def translateRestriction (sol : Solution t f G c) {U V : (Opens X)ᵒᵖ} (rho : U ⟶ V) :
    translateSectionRing E α δ sol U ⟶ translateSectionRing E α δ sol V :=
  CommRingCat.ofHom
    (Ideal.Quotient.lift (translateGraphIdeal E α δ sol U)
      ((Ideal.Quotient.mk (translateGraphIdeal E α δ sol V)).comp
        (translateTrivRestriction E α sol rho).hom) sorry)

/-- The presheaf of pushout rings `𝒪_{X'_ξ}`. -/
def translatePresheaf (sol : Solution t f G c) : TopCat.Presheaf CommRingCat.{u} X where
  obj U := translateSectionRing E α δ sol U
  map rho := translateRestriction E α δ sol rho
  map_id U := sorry
  map_comp rho sigma := sorry

/-- The pushout presheaf of `𝒪_{X'_ξ}` is a sheaf. -/
theorem translatePresheaf_isSheaf (sol : Solution t f G c) :
    (translatePresheaf E α δ sol).IsSheaf := sorry

/-- The structure sheaf of the pushout translate `X'_ξ`. -/
def translateSheaf (sol : Solution t f G c) : TopCat.Sheaf CommRingCat.{u} X :=
  ⟨translatePresheaf E α δ sol, translatePresheaf_isSheaf E α δ sol⟩

/-- The ringed space `X'_ξ` with the same underlying space as `X` and structure sheaf the
pushout of `f⁻¹ 𝒪_{S'}[ℰ]` along `ψ`. -/
def translateSpace (sol : Solution t f G c) : RingedSpace.{u} :=
  (translateSheaf E α δ sol).toRingedSpace

/-- The structure-sheaf map `𝒪_{X'_ξ} ⟶ 𝒪_X` of the translated thickening. -/
def translateISharp (sol : Solution t f G c) :
    translateSheaf E α δ sol ⟶ X.sheaf :=
  ObjectProperty.homMk
    { app U :=
        CommRingCat.ofHom
          (Ideal.Quotient.lift (translateGraphIdeal E α δ sol U)
            (((evalToX E α sol).hom.app U).hom.comp (translateFstRingHom E α sol U)) sorry)
      naturality {_ _} rho := sorry }

/-- The first-order thickening `i : X ⟶ X'_ξ`. -/
def translateI (sol : Solution t f G c) : X ⟶ translateSpace E α δ sol :=
  InducedCategory.homMk
    { base := 𝟙 X.carrier
      c := (translateISharp E α δ sol).hom }

/-- The translated thickening `X ⟶ X'_ξ` is first-order. -/
instance instIsFirstOrderThickening_translateI (sol : Solution t f G c) :
    IsFirstOrderThickening (translateI E α δ sol) := sorry

/-- The structure-sheaf map `𝒪_{S'} ⟶ (sol.i ≫ sol.f')_* 𝒪_{X'_ξ}`. -/
def translateF'Sharp (sol : Solution t f G c) :
    S'.sheaf ⟶
      (TopCat.Sheaf.pushforward CommRingCat.{u} (sol.i ≫ sol.f').hom.base).obj
        (translateSheaf E α δ sol) :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
      (sol.i ≫ sol.f').hom.base).homEquiv S'.sheaf (translateSheaf E α δ sol))
    (ObjectProperty.homMk
      { app U :=
          CommRingCat.ofHom
            { toFun := fun a ↦
                Ideal.Quotient.mk (translateGraphIdeal E α δ sol U)
                  (TrivSqZeroExt.inl
                    ((FreeAlgebra.base (inverseImageS' sol)
                        (generatorSheaf E α sol)).hom.app U a))
              map_zero' := sorry
              map_one' := sorry
              map_add' := sorry
              map_mul' := sorry }
        naturality {_ _} rho := sorry })

/-- The morphism of ringed spaces `X'_ξ ⟶ S'` of a translated solution. -/
def translateF' (sol : Solution t f G c) : translateSpace E α δ sol ⟶ S' :=
  InducedCategory.homMk
    { base := (sol.i ≫ sol.f').hom.base
      c := (translateF'Sharp E α δ sol).hom }

/-- The `𝒪_{X'_ξ}`-module map `Ker((translateI E α δ sol)^♯) ⟶ (translateI E α δ sol)_* 𝒢`
given by `snd + ψ` on kernel sections. The first component of a lift of such a
section lies in `ker(evalToX)`. -/
def translateKernelToPushforward (sol : Solution t f G c) :
    Hom.kernelIdealSheaf (translateI E α δ sol) ⟶ ((translateI E α δ sol) _*).obj G where
  val :=
    PresheafOfModules.homMk
      { app U :=
          AddCommGrpCat.ofHom <|
            AddMonoidHom.mk'
              (fun x ↦
                let r :=
                  KernelIdeal.ιApp
                    (commRingSheafPushforwardMap (translateI E α δ sol)) U x
                let t := Quotient.out r
                TrivSqZeroExt.snd t +
                  translateKerMap E α δ sol U (TrivSqZeroExt.fst t) sorry)
              sorry
        naturality {_ _} _ := sorry }
      (fun _ _ _ ↦ sorry)

/-- The `𝒪_{X'_ξ}`-module map `(translateI E α δ sol)_* 𝒢 ⟶ Ker((translateI E α δ sol)^♯)`
sending `n` to the class of `inr n`. -/
def translatePushforwardToKernel (sol : Solution t f G c) :
    ((translateI E α δ sol) _*).obj G ⟶ Hom.kernelIdealSheaf (translateI E α δ sol) where
  val :=
    PresheafOfModules.homMk
      { app U :=
          AddCommGrpCat.ofHom <|
            AddMonoidHom.mk'
              (fun n ↦
                (KernelIdeal.sectionsIso
                    (commRingSheafPushforwardMap (translateI E α δ sol)) U).inv
                  ⟨Ideal.Quotient.mk (translateGraphIdeal E α δ sol U)
                    (TrivSqZeroExt.inr n), sorry⟩)
              sorry
        naturality {_ _} _ := sorry }
      (fun _ _ _ ↦ sorry)

/-- Identification of `Ker((translateI E α δ sol)^♯)` with `𝒢`. The forward map is the
pushout projection `snd + ψ`; the inverse sends `n` to the class of `inr n`. -/
def translateKernelIso (sol : Solution t f G c) :
    Hom.idealModule (translateI E α δ sol) ≅ G where
  hom :=
    ((translateI E α δ sol) ^*).map (translateKernelToPushforward E α δ sol) ≫
      (pullbackPushforwardAdjunction (translateI E α δ sol)).counit.app G
  inv :=
    (asIso
        ((pullbackPushforwardAdjunction (translateI E α δ sol)).counit.app G)).inv ≫
      ((translateI E α δ sol) ^*).map (translatePushforwardToKernel E α δ sol)
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Choice-free constructor: the pushout of `f⁻¹ 𝒪_{S'}[E ×_{𝒪_X} i⁻¹ 𝒪_{X'}]` along
`ψ = φ|_{I'} + δ` for an explicit 91.7.2 conormal representative `δ`. -/
def translateOf (sol : Solution t f G c) : Solution t f G c :=
  Solution.of t f G c (translateI E α δ sol) (translateF' E α δ sol) sorry
    (translateKernelIso E α δ sol) sorry

/-- The translate of a solution along an explicit conormal map is again a solution of
91.7.0.1, with structure sheaf the pushout of `f⁻¹ 𝒪_{S'}[ℰ]` along `ψ`. -/
theorem translateOf_spec (sol : Solution t f G c) :
    (translateOf E α δ sol).i = translateI E α δ sol ∧
      (translateOf E α δ sol).f' = translateF' E α δ sol ∧
        (translateOf E α δ sol).kernelIso = translateKernelIso E α δ sol := sorry

end Of

/-- The 91.7.2 generator sheaf of a class ξ, chosen from `exists_conormalHomClass`. -/
def translateGenerators
    (ξ : Ext⁽(1 : ℤ)⁾((moduleQ X).obj NL[f],
      (moduleQ X).obj ((CochainComplex.singleFunctor X.Modules 0).obj G))) :
    Sheaf (Opens.grothendieckTopology X) (Type u) :=
  Classical.choose
    (TopCat.Sheaf.NaiveCotangent.exists_conormalHomClass
      (B := inverseImageStructureSheafUnder f) G ξ)

/-- The 91.7.2 generator assignment of a class ξ. -/
def translateAssign
    (ξ : Ext⁽(1 : ℤ)⁾((moduleQ X).obj NL[f],
      (moduleQ X).obj ((CochainComplex.singleFunctor X.Modules 0).obj G))) :
    translateGenerators ξ ⟶
      FreeAlgebra.Presentation.generators (inverseImageStructureSheafUnder f) :=
  Classical.choose
    (Classical.choose_spec
      (TopCat.Sheaf.NaiveCotangent.exists_conormalHomClass
        (B := inverseImageStructureSheafUnder f) G ξ))

/-- The 91.7.2 conormal map of a class ξ. -/
def translateConormal
    (ξ : Ext⁽(1 : ℤ)⁾((moduleQ X).obj NL[f],
      (moduleQ X).obj ((CochainComplex.singleFunctor X.Modules 0).obj G))) :
    (Presentation.ofGenerators (translateGenerators ξ) (translateAssign ξ)).X (-1) ⟶ G :=
  Classical.choose
    (Classical.choose_spec
      (Classical.choose_spec
        (TopCat.Sheaf.NaiveCotangent.exists_conormalHomClass
          (B := inverseImageStructureSheafUnder f) G ξ))).2

/-- `translateGenerators`, `translateAssign`, and `translateConormal` are a locally
surjective 91.7.2 representative of ξ. -/
theorem translateConormal_spec
    (ξ : Ext⁽(1 : ℤ)⁾((moduleQ X).obj NL[f],
      (moduleQ X).obj ((CochainComplex.singleFunctor X.Modules 0).obj G))) :
    IsLocallySurjective
        (FreeAlgebra.evaluation (inverseImageStructureSheafUnder f)
          (translateGenerators ξ) (translateAssign ξ)).right ∧
      Presentation.derivedComparison (translateGenerators ξ) (translateAssign ξ) ≫ ξ =
        TopCat.Sheaf.NaiveCotangent.conormalHomClass G
          (translateGenerators ξ) (translateAssign ξ) (translateConormal ξ) := sorry

/-- Pushout translate of a solution along an Ext¹ class, using a 91.7.2 conormal
representative internally. -/
def translate
    (ξ : Ext⁽(1 : ℤ)⁾((moduleQ X).obj NL[f],
      (moduleQ X).obj ((CochainComplex.singleFunctor X.Modules 0).obj G)))
    (sol : Solution t f G c) :
    Solution t f G c :=
  translateOf (translateGenerators ξ) (translateAssign ξ) (translateConormal ξ) sol

/-- `translate ξ sol` is `translateOf` of a locally surjective 91.7.2 representative of ξ. -/
theorem translate_spec
    (ξ : Ext⁽(1 : ℤ)⁾((moduleQ X).obj NL[f],
      (moduleQ X).obj ((CochainComplex.singleFunctor X.Modules 0).obj G)))
    (sol : Solution t f G c) :
    ∃ (E : Sheaf (Opens.grothendieckTopology X) (Type u))
      (α : E ⟶ FreeAlgebra.Presentation.generators (inverseImageStructureSheafUnder f))
      (δ : (Presentation.ofGenerators E α).X (-1) ⟶ G),
        IsLocallySurjective
            (FreeAlgebra.evaluation (inverseImageStructureSheafUnder f) E α).right ∧
          Presentation.derivedComparison E α ≫ ξ =
              TopCat.Sheaf.NaiveCotangent.conormalHomClass G E α δ ∧
            translate ξ sol = translateOf E α δ sol := sorry

end Solution
end AlgebraicGeometry.RingedSpace.Thickening


