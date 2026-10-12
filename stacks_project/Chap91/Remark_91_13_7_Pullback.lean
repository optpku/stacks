/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap91.Remark_91_13_7_Pushout
public import stacks_project.Chap91.Remark_91_13_5_Presentation

/-!
# Pullback of a square-zero f⁻¹O_B-algebra extension along g^♯

In the identity-base setting of Lemma 91.13.6, the source constructs O'_2 by
pulling 0 ⟶ G ⟶ O_{D'} ⟶ O_D ⟶ 0 back along g^♯ : g⁻¹ O_C ⟶ O_D, as the
fibre product O_{D'} ×_{O_D} O_C.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf
open SheafOfModules.RingedSite
open SheafOfModules.RingedSite.FirstOrderThickening
open SheafOfModules.RingedSite.FirstOrderThickening.Solution
open SheafOfModules.RingedSite.NaiveCotangent
open scoped SheafOfModules.RingedSite
open scoped CategoryTheory.Sheaf.FreeAlgebra

noncomputable section

universe u

namespace SheafOfModules.RingedSite.FirstOrderThickening
namespace Solution

-- Local instance justification (defeq pin): `moduleCat_hasDerivedCategory` is reducible to `HasDerivedCategory.standard` and is not global; `ModuleDerived`, `singleFunctor`, and Ext must share that same derived-category instance.
attribute [local instance] RingedSite.Hom.moduleCat_hasDerivedCategory
-- Local instance justification (defeq pin): the commutative-sheaf presentation uses the same standard derived-category owner, exposed through the site-level spelling.
attribute [local instance] SheafOfModules.RingedSite.moduleCategoryHasDerivedCategory

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
variable [HasWeakSheafify J CommRingCat.{u}]
variable [J.WEqualsLocallyBijective CommRingCat.{u}]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {O_B O_C O_D : Sheaf J CommRingCat.{u}}
variable {fSharp : O_B ⟶ O_C} {gSharp : O_C ⟶ O_D}
variable {G : SheafOfModules (ringSheaf J O_D)}

/-- The projection `O'_2 ⟶ O_C` of the ring-sheaf fibre product is locally surjective. -/
instance instIsLocallySurjective_pullback_snd
    (SD :
      Solution (𝟙 O_B) (isSquareZero_id O_B) (fSharp ≫ gSharp) G
        (zeroKernelMap (fSharp ≫ gSharp) G)) :
    Sheaf.IsLocallySurjective (Limits.pullback.snd SD.proj gSharp) := sorry

/-- The projection `O'_2 ⟶ O_C` is a square-zero extension. -/
theorem isSquareZero_pullback_snd
    (SD :
      Solution (𝟙 O_B) (isSquareZero_id O_B) (fSharp ≫ gSharp) G
        (zeroKernelMap (fSharp ≫ gSharp) G)) :
    KernelIdeal.IsSquareZero (Limits.pullback.snd SD.proj gSharp) := sorry

/-- Kernel identification of the fibre product with the restricted coefficient module. -/
def kernelIso_pullbackAlong
    (SD :
      Solution (𝟙 O_B) (isSquareZero_id O_B) (fSharp ≫ gSharp) G
        (zeroKernelMap (fSharp ≫ gSharp) G)) :
    (isSquareZero_pullback_snd SD).targetModule
        (KernelIdeal.quotientComparison_isIso (Limits.pullback.snd SD.proj gSharp)) ≅
      (restrictionAlong gSharp).obj G where
  hom :=
    { val :=
        PresheafOfModules.homMk
          { app U :=
              AddCommGrpCat.ofHom <|
                AddMonoidHom.mk'
                  (fun x ↦
                    (SD.kernelIso.hom).val.app U
                      ((SD.proj_squareZero.targetModuleForgetIso
                            SD.proj_quotient_isIso).inv.hom.app U
                        ((KernelIdeal.sectionsIso SD.proj U).inv
                          ⟨(Limits.pullback.fst SD.proj gSharp).hom.app U
                              (KernelIdeal.ιApp (Limits.pullback.snd SD.proj gSharp) U
                                (((isSquareZero_pullback_snd SD).targetModuleForgetIso
                                      (KernelIdeal.quotientComparison_isIso
                                        (Limits.pullback.snd SD.proj gSharp))).hom.hom.app U x)),
                            sorry⟩)))
                  sorry
            naturality {_ _} _ := sorry }
          (fun _ _ _ ↦ sorry) }
  inv :=
    { val :=
        PresheafOfModules.homMk
          { app U :=
              AddCommGrpCat.ofHom <|
                AddMonoidHom.mk'
                  (fun n ↦
                    ((isSquareZero_pullback_snd SD).targetModuleForgetIso
                          (KernelIdeal.quotientComparison_isIso
                            (Limits.pullback.snd SD.proj gSharp))).inv.hom.app
                      U ((KernelIdeal.sectionsIso (Limits.pullback.snd SD.proj gSharp) U).inv
                        ⟨pullbackSectionMk SD.proj gSharp U
                            (KernelIdeal.ιApp SD.proj U
                              ((SD.proj_squareZero.targetModuleForgetIso
                                    SD.proj_quotient_isIso).hom.hom.app U
                                ((SD.kernelIso.inv).val.app U n)))
                            0 sorry,
                          sorry⟩))
                  sorry
            naturality {_ _} _ := sorry }
          (fun _ _ _ ↦ sorry) }
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Pullback of `0 ⟶ G ⟶ O_{D'} ⟶ O_D ⟶ 0` along `gSharp`, as a square-zero
`f⁻¹ O_B`-algebra extension of `O_C` by the restriction of `G`. -/
def pullbackAlong
    (SD :
      Solution (𝟙 O_B) (isSquareZero_id O_B) (fSharp ≫ gSharp) G
        (zeroKernelMap (fSharp ≫ gSharp) G)) :
    Solution (𝟙 O_B) (isSquareZero_id O_B) fSharp
      ((restrictionAlong gSharp).obj G)
      (zeroKernelMap fSharp ((restrictionAlong gSharp).obj G)) :=
  { middle := Limits.pullback SD.proj gSharp
    proj := Limits.pullback.snd SD.proj gSharp
    structureMap := Limits.pullback.lift SD.structureMap fSharp SD.commutes
    proj_locallySurjective := instIsLocallySurjective_pullback_snd SD
    proj_squareZero := isSquareZero_pullback_snd SD
    proj_quotient_isIso := KernelIdeal.quotientComparison_isIso (Limits.pullback.snd SD.proj gSharp)
    commutes := sorry
    kernelIso := kernelIso_pullbackAlong SD
    induces_c := sorry }

/-- The carrier of `pullbackAlong` is the ring-sheaf fibre product `O_{D'} ×_{O_D} O_C`. -/
theorem pullbackAlong_middle
    (SD :
      Solution (𝟙 O_B) (isSquareZero_id O_B) (fSharp ≫ gSharp) G
        (zeroKernelMap (fSharp ≫ gSharp) G)) :
    (pullbackAlong SD).middle = Limits.pullback SD.proj gSharp := sorry

/-- The projection of `pullbackAlong` is the second projection of the fibre product. -/
theorem pullbackAlong_proj
    (SD :
      Solution (𝟙 O_B) (isSquareZero_id O_B) (fSharp ≫ gSharp) G
        (zeroKernelMap (fSharp ≫ gSharp) G)) :
    (pullbackAlong SD).proj = Limits.pullback.snd SD.proj gSharp := sorry

/-- The structure map of `pullbackAlong` is the fibre-product lift of `SD.structureMap`
and `fSharp`. -/
theorem pullbackAlong_structureMap
    (SD :
      Solution (𝟙 O_B) (isSquareZero_id O_B) (fSharp ≫ gSharp) G
        (zeroKernelMap (fSharp ≫ gSharp) G)) :
    (pullbackAlong SD).structureMap = Limits.pullback.lift SD.structureMap fSharp SD.commutes :=
  sorry

/-- The identity-base connecting diagram from the pullback along `gSharp` to `O_{D'}`. -/
def pullbackAlongDiagram
    (SD :
      Solution (𝟙 O_B) (isSquareZero_id O_B) (fSharp ≫ gSharp) G
        (zeroKernelMap (fSharp ≫ gSharp) G)) :
    RelativeDiagram (pullbackAlong SD).proj (𝟙 O_B) SD.proj (𝟙 O_B) :=
  RelativeDiagram.of fSharp (pullbackAlong SD).structureMap (pullbackAlong SD).commutes
    (fSharp ≫ gSharp) SD.structureMap SD.commutes gSharp (𝟙 O_B) (𝟙 O_B) sorry
    (Category.id_comp (fSharp ≫ gSharp))
    (kernelIdealHom (pullbackAlong SD) ≫
      (restrictionAlong gSharp).map (SD.kernelIso.inv ≫ (idealTargetIso SD).inv))
    sorry

/-- `pullbackAlongDiagram` has `g = gSharp` and identity maps on `O_B`. -/
theorem pullbackAlongDiagram_spec
    (SD :
      Solution (𝟙 O_B) (isSquareZero_id O_B) (fSharp ≫ gSharp) G
        (zeroKernelMap (fSharp ≫ gSharp) G)) :
    (pullbackAlongDiagram SD).g = gSharp ∧
      (pullbackAlongDiagram SD).t = 𝟙 O_B ∧
      (pullbackAlongDiagram SD).t' = 𝟙 O_B := sorry

/-- The vertical map `O'_2 ⟶ O_{D'}` in the source pullback square. -/
def fromPullbackAlong
    (SD :
      Solution (𝟙 O_B) (isSquareZero_id O_B) (fSharp ≫ gSharp) G
        (zeroKernelMap (fSharp ≫ gSharp) G)) :
    FittingMap (pullbackAlongDiagram SD) :=
  FittingMap.of (Limits.pullback.fst SD.proj gSharp) sorry sorry sorry

/-- `fromPullbackAlong` is the first projection of the fibre product. -/
theorem fromPullbackAlong_hom
    (SD :
      Solution (𝟙 O_B) (isSquareZero_id O_B) (fSharp ≫ gSharp) G
        (zeroKernelMap (fSharp ≫ gSharp) G)) :
    (fromPullbackAlong SD).hom = Limits.pullback.fst SD.proj gSharp := sorry

/-- The source assignment `φ : E' ⟶ E` of the pullback presentation square, as the
underlying sheaf of sets of `pullback.fst`. -/
def pullbackAlong_presentation
    (SD :
      Solution (𝟙 O_B) (isSquareZero_id O_B) (fSharp ≫ gSharp) G
        (zeroKernelMap (fSharp ≫ gSharp) G)) :
    underlyingSets (pullbackAlong SD) ⟶ underlyingSets SD :=
  (sheafForget J).map (Limits.pullback.fst SD.proj gSharp)

/-- `pullbackAlong_presentation` is the underlying map of `pullback.fst`. -/
theorem pullbackAlong_presentation_eq
    (SD :
      Solution (𝟙 O_B) (isSquareZero_id O_B) (fSharp ≫ gSharp) G
        (zeroKernelMap (fSharp ≫ gSharp) G)) :
    pullbackAlong_presentation SD =
      (sheafForget J).map (Limits.pullback.fst SD.proj gSharp) := sorry

/-- The morphism of presentations `NL(α) ⟶ NL(β)` induced by
`pullbackAlong_presentation`, with target map `gSharp`. -/
def pullbackAlong_presentationHom
    (SD :
      Solution (𝟙 O_B) (isSquareZero_id O_B) (fSharp ≫ gSharp) G
        (zeroKernelMap (fSharp ≫ gSharp) G)) :
    Presentation.Hom
      (FreeAlgebra.base O_B (underlyingSets (pullbackAlong SD)))
      (eval (underlyingSets (pullbackAlong SD))
        (assignOf (pullbackAlong SD) (underlyingSets (pullbackAlong SD))
          (underlyingAssign' (pullbackAlong SD))))
      (FreeAlgebra.base O_B (underlyingSets SD))
      (eval (underlyingSets SD)
        (assignOf SD (underlyingSets SD) (underlyingAssign' SD))) where
  base := 𝟙 O_B
  middle :=
    (FreeAlgebra.evaluation (Under.mk (FreeAlgebra.base O_B (underlyingSets SD)))
        (underlyingSets (pullbackAlong SD))
        (pullbackAlong_presentation SD ≫
          FreeAlgebra.generator O_B (underlyingSets SD))).right
  target := gSharp
  baseSq := ⟨sorry⟩
  targetSq := ⟨sorry⟩

/-- The map of presentation complexes `NL(α) ⟶ NL(β)` induced by
`pullbackAlong_presentation`. -/
def pullbackAlong_naiveCotangentMap
    (SD :
      Solution (𝟙 O_B) (isSquareZero_id O_B) (fSharp ≫ gSharp) G
        (zeroKernelMap (fSharp ≫ gSharp) G)) :
    (extendComplex gSharp).obj
        (Presentation.ofGenerators (underlyingSets (pullbackAlong SD))
          (assignOf (pullbackAlong SD) (underlyingSets (pullbackAlong SD))
            (underlyingAssign' (pullbackAlong SD)))) ⟶
      Presentation.ofGenerators (underlyingSets SD)
        (assignOf SD (underlyingSets SD) (underlyingAssign' SD)) :=
  Presentation.Hom.map (pullbackAlong_presentationHom SD)

/-- `pullbackAlong_naiveCotangentMap` is `Presentation.Hom.map` of
`pullbackAlong_presentationHom`. -/
theorem pullbackAlong_naiveCotangentMap_spec
    (SD :
      Solution (𝟙 O_B) (isSquareZero_id O_B) (fSharp ≫ gSharp) G
        (zeroKernelMap (fSharp ≫ gSharp) G)) :
    pullbackAlong_naiveCotangentMap SD =
      Presentation.Hom.map (pullbackAlong_presentationHom SD) := sorry

/-- The degree `-1` map `φbar : J/J² ⟶ K/K²` induced by `pullbackAlong_presentation`. -/
def pullbackAlong_conormalMap
    (SD :
      Solution (𝟙 O_B) (isSquareZero_id O_B) (fSharp ≫ gSharp) G
        (zeroKernelMap (fSharp ≫ gSharp) G)) :
    (extendAlong gSharp).obj
        ((Presentation.ofGenerators (underlyingSets (pullbackAlong SD))
            (assignOf (pullbackAlong SD) (underlyingSets (pullbackAlong SD))
              (underlyingAssign' (pullbackAlong SD)))).X (-1)) ⟶
      (Presentation.ofGenerators (underlyingSets SD)
          (assignOf SD (underlyingSets SD) (underlyingAssign' SD))).X (-1) :=
  (pullbackAlong_naiveCotangentMap SD).f (-1)

/-- `pullbackAlong_conormalMap` is degree `-1` of `pullbackAlong_naiveCotangentMap`. -/
theorem pullbackAlong_conormalMap_spec
    (SD :
      Solution (𝟙 O_B) (isSquareZero_id O_B) (fSharp ≫ gSharp) G
        (zeroKernelMap (fSharp ≫ gSharp) G)) :
    pullbackAlong_conormalMap SD = (pullbackAlong_naiveCotangentMap SD).f (-1) := sorry

/-- The conormal map of `O'_2` is the conormal map of `O_{D'}` composed with the
degree `-1` map of `NL(α) ⟶ NL(β)` induced by `pullbackAlong_presentation`. -/
theorem pullbackAlong_conormal_comp
    (SD :
      Solution (𝟙 O_B) (isSquareZero_id O_B) (fSharp ≫ gSharp) G
        (zeroKernelMap (fSharp ≫ gSharp) G)) :
    conormalHom (pullbackAlong SD) (underlyingSets (pullbackAlong SD))
        (underlyingAssign' (pullbackAlong SD))
        (assignOf (pullbackAlong SD) (underlyingSets (pullbackAlong SD))
          (underlyingAssign' (pullbackAlong SD))) rfl =
      (extendRestrictAdj gSharp).homEquiv
          ((Presentation.ofGenerators (underlyingSets (pullbackAlong SD))
              (assignOf (pullbackAlong SD) (underlyingSets (pullbackAlong SD))
                (underlyingAssign' (pullbackAlong SD)))).X (-1))
          ((Presentation.ofGenerators (underlyingSets SD)
              (assignOf SD (underlyingSets SD) (underlyingAssign' SD))).X (-1))
          (pullbackAlong_conormalMap SD) ≫
        (restrictionAlong gSharp).map
          (conormalHom SD (underlyingSets SD) (underlyingAssign' SD)
            (assignOf SD (underlyingSets SD) (underlyingAssign' SD)) rfl) :=
  sorry

/-- The identity presentation of `O'_2` has locally surjective evaluation. -/
instance instIsLocallySurjective_eval_pullbackAlong
    (SD :
      Solution (𝟙 O_B) (isSquareZero_id O_B) (fSharp ≫ gSharp) G
        (zeroKernelMap (fSharp ≫ gSharp) G)) :
    Sheaf.IsLocallySurjective
      (FreeAlgebra.evaluation (Under.mk fSharp)
        (underlyingSets (pullbackAlong SD))
        (assignOf (pullbackAlong SD) (underlyingSets (pullbackAlong SD))
          (underlyingAssign' (pullbackAlong SD)))).right :=
  underlying_eval_isLocallySurjective (pullbackAlong SD)

/-- The identity presentation of `O_{D'}` has locally surjective evaluation. -/
instance instIsLocallySurjective_eval_SD
    (SD :
      Solution (𝟙 O_B) (isSquareZero_id O_B) (fSharp ≫ gSharp) G
        (zeroKernelMap (fSharp ≫ gSharp) G)) :
    Sheaf.IsLocallySurjective
      (FreeAlgebra.evaluation (Under.mk (fSharp ≫ gSharp))
        (underlyingSets SD) (assignOf SD (underlyingSets SD)
          (underlyingAssign' SD))).right :=
  underlying_eval_isLocallySurjective SD

/-- The presentation complex map induced by `pullbackAlong_presentation` represents
`naiveCotangentComparison` after the cochain-counit, `pullbackComplexExtendIso`,
and the derived presentation identifications of `NL(α)` and `NL(β)`. -/
theorem pullbackAlong_naiveCotangentMap_comparison
    (SD :
      Solution (𝟙 O_B) (isSquareZero_id O_B) (fSharp ≫ gSharp) G
        (zeroKernelMap (fSharp ≫ gSharp) G)) :
    (SameSite.pullbackDerived gSharp).map
        (Presentation.derivedComparisonIso
            (underlyingSets (pullbackAlong SD))
            (assignOf (pullbackAlong SD) (underlyingSets (pullbackAlong SD))
              (underlyingAssign' (pullbackAlong SD)))).hom ≫
      naiveCotangentComparison fSharp gSharp =
      (Functor.LeftDerived.Homotopy.cochainCounit
            ((sameSiteHom gSharp).modulePullback)).app
          (Presentation.ofGenerators (underlyingSets (pullbackAlong SD))
            (assignOf (pullbackAlong SD) (underlyingSets (pullbackAlong SD))
              (underlyingAssign' (pullbackAlong SD)))) ≫
        (moduleQ O_D).map
          ((pullbackComplexExtendIso gSharp).hom.app
              (Presentation.ofGenerators (underlyingSets (pullbackAlong SD))
                (assignOf (pullbackAlong SD) (underlyingSets (pullbackAlong SD))
                  (underlyingAssign' (pullbackAlong SD)))) ≫
            pullbackAlong_naiveCotangentMap SD) ≫
          (Presentation.derivedComparisonIso (underlyingSets SD)
              (assignOf SD (underlyingSets SD) (underlyingAssign' SD))).hom :=
  sorry

end Solution
end SheafOfModules.RingedSite.FirstOrderThickening
