/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap85.Lemma_85_6_1_Fiber
public import stacks_project.Chap85.Lemma_85_6_1_LowerShriek
public import stacks_project.Chap85.Lemma_85_6_1_Ringed

/-!
# Lemma 85.6.1

In Situation 85.3.3 a sheaf of rings `O` on `C_total` yields a canonical morphism of
ringed topoi `g_n : (Sh(C_n), O_n) ⟶ (Sh(C_total), O)` agreeing with Lemma 85.3.5 on
underlying topoi. The functor `g_n^* : Mod(O) ⥤ Mod(O_n)` has a left adjoint `g_{n!}`,
and the restriction of `g_{n!} G` to `C_m` is `⊕_{φ : n ⟶ m} f_φ^* G`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open RingedSite

noncomputable section

universe u v w

namespace CategoryTheory.SimplicialSites

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [IsMorphismDiagram C J]
variable (O : Sheaf (topology C J) RingCat.{w})
variable [(topology C J).HasSheafCompose (forget RingCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (forget RingCat.{w})]
variable [∀ n, HasSheafify ((J n).toGrothendieck) (Type w)]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ Type w,
    (ofStage C n).op.HasPointwiseRightKanExtension P]
variable [HasWeakSheafify (topology C J) (Type w)]
variable [∀ n, (SheafOfModules.restrictScalars.{w}
    (stageMorphism C J O n).structureMap).IsRightAdjoint]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    (SheafOfModules.restrictScalars.{w} (ringedToposMap C J O φ).structureMap).IsRightAdjoint]

/-- Lemma 85.6.1 (1): In Situation 85.3.3, a sheaf of rings `O` on `C_total` yields a
canonical morphism of ringed topoi `g_n : (Sh(C_n), O_n) ⟶ (Sh(C_total), O)` agreeing
with the morphism `g_n` of Lemma 85.3.5 on underlying topoi. -/
@[stacks 0D72]
def ringedOfStageMorphism (n : SimplexCategory) :
    ToposHom (componentRingedSite C J O n) (totalRingedSite C J O) :=
  stageMorphism C J O n

/-- The underlying topos morphism of `ringedOfStageMorphism` is `ofStageMorphism`. -/
theorem ringedOfStageMorphism_toTopos (n : SimplexCategory) :
    (ringedOfStageMorphism C J O n).toTopos = ofStageMorphism C J n :=
  sorry

/-- Lemma 85.6.1 (2): the functor `g_n^* : Mod(O) ⥤ Mod(O_n)` has a left adjoint `g_{n!}`. -/
@[stacks 0D72, instance]
instance ringedOfStageMorphism_modulePullback_isRightAdjoint (n : SimplexCategory) :
    ((stageMorphism C J O n).modulePullback).IsRightAdjoint :=
  (moduleLowerShriek.adjunction C J O n).ofNatIsoRight
    (moduleInverseImageIsoModulePullback C J O n) |>.isRightAdjoint

/-- Lemma 85.6.1 (3): for `G` in `Mod(O_n)` the restriction of `g_{n!} G` to `C_m` is
`⊕_{φ : n ⟶ m} f_φ^* G`, where `f_φ : (Sh(C_m), O_m) ⟶ (Sh(C_n), O_n)` is the morphism
of ringed topoi agreeing with the previously defined `f_φ` on topoi and using
`O(φ) : f_φ⁻¹ O_n ⟶ O_m` on sheaves of rings. -/
@[stacks 0D72]
def moduleLowerShriek_componentCoproduct (n m : SimplexCategory)
    [HasColimitsOfShape (Discrete (n ⟶ m))
      (SheafOfModules.{w} (componentRingSheaf C J O m))]
    (G : SheafOfModules.{w} (componentRingSheaf C J O n)) :
    (stageMorphism C J O m).modulePullback.obj ((moduleLowerShriek C J O n).obj G) ≅
      ∐ fun φ : n ⟶ m ↦ (ringedToposMap C J O φ).modulePullback.obj G :=
  (moduleLowerShriek_componentBiproductIso C J O n m G).symm

/-- The restriction identification is the inverse of the coproduct comparison iso. -/
theorem moduleLowerShriek_componentCoproduct_eq (n m : SimplexCategory)
    [HasColimitsOfShape (Discrete (n ⟶ m))
      (SheafOfModules.{w} (componentRingSheaf C J O m))]
    (G : SheafOfModules.{w} (componentRingSheaf C J O n)) :
    moduleLowerShriek_componentCoproduct C J O n m G =
      (moduleLowerShriek_componentBiproductIso C J O n m G).symm :=
  sorry

end CategoryTheory.SimplicialSites

namespace CategoryTheory.Grothendieck

variable (F : SimplicialObject Cat.{v, u}) (J : ∀ n, Precoverage (F.obj n))
variable [IsFiberwiseSite F J]
variable (O : Sheaf (topology F J) RingCat.{w})
variable [(topology F J).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
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

/-- Lemma 85.6.1 (4): In Situation 85.3.3 case B, a sheaf of rings `O` on `C_total` yields a
canonical morphism of ringed topoi `g_n : (Sh(C_n), O_n) ⟶ (Sh(C_total), O)` agreeing
with the morphism `g_n` of Lemma 85.3.5 on underlying topoi. -/
@[stacks 0D72]
def fiberRingedOfStageMorphism (n : SimplexCategory) :
    ToposHom (fiberComponentRingedSite F J O n) (fiberTotalRingedSite F J O) :=
  fiberStageMorphism F J O n

/-- The underlying topos morphism of `fiberRingedOfStageMorphism` is `fiberMorphism`. -/
theorem fiberRingedOfStageMorphism_toTopos (n : SimplexCategory) :
    (fiberRingedOfStageMorphism F J O n).toTopos = fiberMorphism F J n :=
  sorry

/-- Lemma 85.6.1 (5): in case B the functor `g_n^* : Mod(O) ⥤ Mod(O_n)` has a left adjoint
`g_{n!}`. -/
@[stacks 0D72, instance]
instance fiberRingedOfStageMorphism_modulePullback_isRightAdjoint (n : SimplexCategory) :
    ((fiberStageMorphism F J O n).modulePullback).IsRightAdjoint :=
  (fiberModuleLowerShriek.adjunction F J O n).ofNatIsoRight
    (fiberModuleInverseImageIsoModulePullback F J O n) |>.isRightAdjoint

/-- Lemma 85.6.1 (6): in case B, for `G` in `Mod(O_n)` the restriction of `g_{n!} G` to `C_m`
is `⊕_{φ : n ⟶ m} f_φ^* G`. -/
@[stacks 0D72]
def fiberModuleLowerShriek_componentCoproduct (n m : SimplexCategory)
    [HasColimitsOfShape (Discrete (n ⟶ m))
      (SheafOfModules.{w} (fiberComponentRingSheaf F J O m))]
    (G : SheafOfModules.{w} (fiberComponentRingSheaf F J O n)) :
    (fiberStageMorphism F J O m).modulePullback.obj ((fiberModuleLowerShriek F J O n).obj G) ≅
      ∐ fun φ : n ⟶ m ↦ (fiberRingedToposMap F J O φ).modulePullback.obj G :=
  (fiberModuleLowerShriek_componentBiproductIso F J O n m G).symm

/-- The case B restriction identification is the inverse of the coproduct comparison iso. -/
theorem fiberModuleLowerShriek_componentCoproduct_eq (n m : SimplexCategory)
    [HasColimitsOfShape (Discrete (n ⟶ m))
      (SheafOfModules.{w} (fiberComponentRingSheaf F J O m))]
    (G : SheafOfModules.{w} (fiberComponentRingSheaf F J O n)) :
    fiberModuleLowerShriek_componentCoproduct F J O n m G =
      (fiberModuleLowerShriek_componentBiproductIso F J O n m G).symm :=
  sorry

end CategoryTheory.Grothendieck
