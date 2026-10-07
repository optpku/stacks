module

public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap85.Lemma_85_11_2_Complex
public import stacks_project.Chap85.Lemma_85_11_2_Fiberwise

/-!
# Lemma 85.11.2

In Situation 85.3.3, with a morphism of ringed topoi
`a : (Sh(C_total), O) ⟶ (Sh(D), O_D)`, for every `O_D`-module `G` the
alternating-face complex `… → g_{2!}(a_2^* G) → g_{1!}(a_1^* G) → g_{0!}(a_0^* G)`
of `O`-modules on `C_total` is a resolution of `a^* G`. Here `g_{n!}` is as in
Lemma 85.6.1.
-/

@[expose] public section

open CategoryTheory AlgebraicTopology HomologicalComplex Opposite RingedSite
open scoped Simplicial

noncomputable section

universe u v w uD vD

namespace CategoryTheory.SimplicialSites

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [IsMorphismDiagram C J]
variable (O : Sheaf (topology C J) RingCat.{w})
variable [(topology C J).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [(topology C J).HasSheafCompose (CategoryTheory.forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (CategoryTheory.forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [∀ n, HasSheafify ((J n).toGrothendieck) (Type w)]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ Type w,
    (ofStage C n).op.HasPointwiseRightKanExtension P]
variable [HasWeakSheafify (topology C J) (Type w)]
variable [∀ n, (SheafOfModules.restrictScalars.{w}
    (stageMorphism C J O n).structureMap).IsRightAdjoint]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    (SheafOfModules.restrictScalars.{w} (ringedToposMap C J O φ).structureMap).IsRightAdjoint]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [HasWeakSheafify (topology C J) AddCommGrpCat.{w}]
variable [∀ n, HasSheafify ((J n).toGrothendieck) AddCommGrpCat.{w}]
variable [HasSheafify (topology C J) AddCommGrpCat.{w}]
variable [∀ n, ((J n).toGrothendieck).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [(topology C J).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable {D : RingedSite.{uD, vD, w}}
variable [D.siteTopology.HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable (a : ToposHom (totalRingedSite C J O) D)
variable [(SheafOfModules.restrictScalars.{w} a.structureMap).IsRightAdjoint]
variable [∀ n, (SheafOfModules.restrictScalars.{w}
    ((stageMorphism C J O n).comp a).structureMap).IsRightAdjoint]
variable (G : SheafOfModules.{w} D.structureSheaf)

/-- Lemma 85.11.2 (1): in Situation 85.3.3 case A, with a morphism of ringed topoi
`a : (Sh(C_total), O) ⟶ (Sh(D), O_D)`, the complex
`… → g_{2!}(a_2^* G) → g_{1!}(a_1^* G) → g_{0!}(a_0^* G)` of `O`-modules on
`C_total`, with differentials the alternating face sums, is a resolution of
`a^* G`. Here `g_{n!}` is as in Lemma 85.6.1. -/
@[stacks 0D7C, instance]
instance modulePullbackAugmentation_quasiIso :
    QuasiIso
      (modulePullbackAugmentation C J O a G :
        modulePullbackComplex C J O a G ⟶
          (ChainComplex.single₀ _).obj (a.modulePullback.obj G)) :=
  sorry

end CategoryTheory.SimplicialSites

namespace CategoryTheory.Grothendieck

variable (F : SimplicialObject Cat.{v, u}) (J : ∀ n, Precoverage (F.obj n))
variable [IsFiberwiseSite F J]
variable (O : Sheaf (topology F J) RingCat.{w})
variable [(topology F J).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [(topology F J).HasSheafCompose (CategoryTheory.forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (CategoryTheory.forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [∀ n, HasSheafify (J n).toGrothendieck (Type w)]
variable [HasSheafify (topology F J) (Type w)]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ Type w,
    (ι F (op n)).op.HasPointwiseRightKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (F.obj (op n))ᵒᵖ ⥤ Type w),
    ((F.map φ.op).toFunctor).op.HasPointwiseRightKanExtension P]
variable [∀ n, (SheafOfModules.restrictScalars.{w}
    (fiberStageMorphism F J O n).structureMap).IsRightAdjoint]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    (SheafOfModules.restrictScalars.{w}
      (fiberRingedToposMap F J O φ).structureMap).IsRightAdjoint]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [HasWeakSheafify (topology F J) AddCommGrpCat.{w}]
variable [∀ n, HasSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [HasSheafify (topology F J) AddCommGrpCat.{w}]
variable [∀ n, ((J n).toGrothendieck).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [(topology F J).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable {D : RingedSite.{uD, vD, w}}
variable [D.siteTopology.HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable (a : ToposHom (fiberTotalRingedSite F J O) D)
variable [(SheafOfModules.restrictScalars.{w} a.structureMap).IsRightAdjoint]
variable [∀ n, (SheafOfModules.restrictScalars.{w}
    ((fiberStageMorphism F J O n).comp a).structureMap).IsRightAdjoint]
variable (G : SheafOfModules.{w} D.structureSheaf)

/-- Lemma 85.11.2 (2): in Situation 85.3.3 case B, with a morphism of ringed topoi
`a : (Sh(C_total), O) ⟶ (Sh(D), O_D)`, the complex
`… → g_{2!}(a_2^* G) → g_{1!}(a_1^* G) → g_{0!}(a_0^* G)` of `O`-modules on
`C_total`, with differentials the alternating face sums, is a resolution of
`a^* G`. Here `g_{n!}` is as in Lemma 85.6.1. -/
@[stacks 0D7C, instance]
instance fiberModulePullbackAugmentation_quasiIso :
    QuasiIso
      (fiberModulePullbackAugmentation F J O a G :
        fiberModulePullbackComplex F J O a G ⟶
          (ChainComplex.single₀ _).obj (a.modulePullback.obj G)) :=
  sorry

end CategoryTheory.Grothendieck
