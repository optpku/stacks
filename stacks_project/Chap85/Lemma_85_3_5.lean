/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap85.Lemma_85_3_5_Stage
public import stacks_project.Chap85.Lemma_85_3_5_Coproduct
public import stacks_project.Chap85.Lemma_85_3_5_Fiber

/-!
# Lemma 85.3.5

In Situation 85.3.3 the degree-`n` inclusion `C_n ⥤ C_total`, `U ↦ U`, is continuous
and cocontinuous. The associated morphism of topoi `g_n : Sh(C_n) ⟶ Sh(C_total)` has
inverse image given by restriction `F ↦ F_n`, that inverse image admits a left adjoint
`g^{Sh}_{n!}` whose restriction to `C_m` is `∐_{φ : n ⟶ m} f_φ⁻¹ G` and which preserves
finite connected limits, and on abelian sheaves the corresponding `g_{n!}` exists,
restricts to `⊕_{φ : n ⟶ m} f_φ⁻¹ G`, and is exact. The same clauses hold in case A
(morphisms of sites) and case B (cocontinuous functors with property P).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.MorphismOfTopoiIn

noncomputable section

universe u v w

namespace CategoryTheory.SimplicialSites

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [IsMorphismDiagram C J]

/-- Lemma 85.3.5 (1): the functor `C_n ⥤ C_total`, `U ↦ U`, is continuous. -/
@[stacks 09WG, instance]
instance ofStage_isContinuous (n : SimplexCategory) :
    (ofStage C n).IsContinuous (J n).toGrothendieck (topology C J) :=
  sorry

/-- Lemma 85.3.5 (2): the functor `C_n ⥤ C_total`, `U ↦ U`, is cocontinuous. -/
@[stacks 09WG, instance]
instance ofStage_isCocontinuous (n : SimplexCategory) :
    (ofStage C n).IsCocontinuous (J n).toGrothendieck (topology C J) :=
  sorry

variable [HasWeakSheafify (topology C J) (Type w)]
variable [∀ n, HasSheafify (J n).toGrothendieck (Type w)]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ Type w, (ofStage C n).op.HasLeftKanExtension P]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ Type w, (ofStage C n).op.HasPointwiseRightKanExtension P]
variable [HasSheafify (topology C J) (Type w)]

/-- Lemma 85.3.5 (3): `g_n⁻¹` associates to a sheaf `F` on `C_total` the sheaf `F_n`
on `C_n`. -/
@[stacks 09WG]
def ofStageMorphism_inverseImage_iso_stageRestrict (n : SimplexCategory) :
    (ofStageMorphism C J n)⁻¹ ≅ stageRestrict C J (Type w) n :=
  CategoryTheory.eqToIso (ofStageMorphism_inverseImage C J n) ≪≫ inverseImageIso C J n

/-- The inverse-image comparison is `eqToIso` of `ofStageMorphism_inverseImage` composed with
`inverseImageIso`. -/
theorem ofStageMorphism_inverseImage_iso_stageRestrict_eq (n : SimplexCategory) :
    ofStageMorphism_inverseImage_iso_stageRestrict C J n =
      CategoryTheory.eqToIso (ofStageMorphism_inverseImage C J n) ≪≫ inverseImageIso C J n :=
  sorry

/-- Lemma 85.3.5 (4): `g_n⁻¹ : Sh(C_total) ⥤ Sh(C_n)` has a left adjoint `g^{Sh}_{n!}`. -/
@[stacks 09WG, instance]
instance stageRestrict_isRightAdjoint (n : SimplexCategory) :
    (stageRestrict C J (Type w) n).IsRightAdjoint :=
  (sheafLowerShriek_adjunction C J n).isRightAdjoint

/-- Lemma 85.3.5 (5): for `G` in `Sh(C_n)` the restriction of `g^{Sh}_{n!} G` to `C_m`
is `∐_{φ : n ⟶ m} f_φ⁻¹ G`. -/
@[stacks 09WG]
def sheafLowerShriek_componentCoproduct (n m : SimplexCategory)
    [HasColimitsOfShape (Discrete (n ⟶ m)) (Sheaf ((J m).toGrothendieck) (Type w))]
    (G : Sheaf ((J n).toGrothendieck) (Type w)) :
    (stageRestrict C J (Type w) m).obj ((sheafLowerShriek C J n).obj G) ≅
      ∐ fun φ : n ⟶ m ↦
        ((C.map φ).toFunctor.sheafPullback (Type w)
          (J n).toGrothendieck (J m).toGrothendieck).obj G :=
  (sheafLowerShriek_componentCoproductIso C J n m G).symm

/-- The type-valued coproduct identification is the inverse of the coproduct comparison iso. -/
theorem sheafLowerShriek_componentCoproduct_eq (n m : SimplexCategory)
    [HasColimitsOfShape (Discrete (n ⟶ m)) (Sheaf ((J m).toGrothendieck) (Type w))]
    (G : Sheaf ((J n).toGrothendieck) (Type w)) :
    sheafLowerShriek_componentCoproduct C J n m G =
      (sheafLowerShriek_componentCoproductIso C J n m G).symm :=
  sorry

/-- Lemma 85.3.5 (6): `g^{Sh}_{n!}` commutes with finite connected limits. -/
@[stacks 09WG, instance]
instance sheafLowerShriek_preservesFiniteConnectedLimits (n : SimplexCategory)
    [∀ P : (C.obj n)ᵒᵖ ⥤ Type w, (ofStage C n).op.HasPointwiseLeftKanExtension P] :
    PreservesFiniteConnectedLimits (sheafLowerShriek C J n) :=
  sorry

variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [HasWeakSheafify (topology C J) AddCommGrpCat.{w}]
variable [HasSheafify (topology C J) AddCommGrpCat.{w}]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ AddCommGrpCat.{w}, (ofStage C n).op.HasLeftKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ AddCommGrpCat.{w}),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]

/-- Lemma 85.3.5 (7): `g_n⁻¹ : Ab(C_total) ⥤ Ab(C_n)` has a left adjoint `g_{n!}`. -/
@[stacks 09WG, instance]
instance abelianStageRestrict_isRightAdjoint (n : SimplexCategory) :
    (stageRestrict C J AddCommGrpCat.{w} n).IsRightAdjoint :=
  (abelianLowerShriek_adjunction C J n).isRightAdjoint

/-- Lemma 85.3.5 (8): for `G` in `Ab(C_n)` the restriction of `g_{n!} G` to `C_m`
is `⊕_{φ : n ⟶ m} f_φ⁻¹ G`. -/
@[stacks 09WG]
def abelianLowerShriek_componentBiproduct (n m : SimplexCategory)
    [HasColimitsOfShape (Discrete (n ⟶ m))
      (Sheaf ((J m).toGrothendieck) AddCommGrpCat.{w})]
    (G : Sheaf ((J n).toGrothendieck) AddCommGrpCat.{w}) :
    (stageRestrict C J AddCommGrpCat.{w} m).obj ((abelianLowerShriek C J n).obj G) ≅
      ∐ fun φ : n ⟶ m ↦
        ((C.map φ).toFunctor.sheafPullback AddCommGrpCat.{w}
          (J n).toGrothendieck (J m).toGrothendieck).obj G :=
  (abelianLowerShriek_componentBiproductIso C J n m G).symm

/-- The abelian direct-sum identification is the inverse of the biproduct comparison iso. -/
theorem abelianLowerShriek_componentBiproduct_eq (n m : SimplexCategory)
    [HasColimitsOfShape (Discrete (n ⟶ m))
      (Sheaf ((J m).toGrothendieck) AddCommGrpCat.{w})]
    (G : Sheaf ((J n).toGrothendieck) AddCommGrpCat.{w}) :
    abelianLowerShriek_componentBiproduct C J n m G =
      (abelianLowerShriek_componentBiproductIso C J n m G).symm :=
  sorry

/-- Lemma 85.3.5 (9): `g_{n!}` is exact. -/
@[stacks 09WG]
theorem abelianLowerShriek_exact (n : SimplexCategory)
    [∀ P : (C.obj n)ᵒᵖ ⥤ AddCommGrpCat.{w},
      (ofStage C n).op.HasPointwiseLeftKanExtension P] :
    exactFunctor
      (Sheaf ((J n).toGrothendieck) AddCommGrpCat.{w})
      (Sheaf (topology C J) AddCommGrpCat.{w})
      (abelianLowerShriek C J n) :=
  sorry

end CategoryTheory.SimplicialSites

namespace CategoryTheory.Grothendieck

variable (F : SimplicialObject Cat.{v, u}) (J : ∀ n, Precoverage (F.obj n))
variable [IsFiberwiseSite F J]

/-- Lemma 85.3.5 (10): the functor `C_n ⥤ C_total`, `U ↦ U`, is continuous in case B. -/
@[stacks 09WG, instance]
instance fiberInclusion_isContinuous (n : SimplexCategory) :
    (ι F (op n)).IsContinuous (J (op n)).toGrothendieck (topology F J) :=
  sorry

/-- Lemma 85.3.5 (11): the functor `C_n ⥤ C_total`, `U ↦ U`, is cocontinuous in case B. -/
@[stacks 09WG, instance]
instance fiberInclusion_isCocontinuous (n : SimplexCategory) :
    (ι F (op n)).IsCocontinuous (J (op n)).toGrothendieck (topology F J) :=
  sorry

variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [HasWeakSheafify (topology F J) (Type w)]
variable [∀ n, HasSheafify (J n).toGrothendieck (Type w)]
variable [HasSheafify (topology F J) (Type w)]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ Type w, (ι F (op n)).op.HasLeftKanExtension P]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ Type w, (ι F (op n)).op.HasPointwiseRightKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (F.obj (op n))ᵒᵖ ⥤ Type w),
    ((F.map φ.op).toFunctor).op.HasPointwiseRightKanExtension P]

/-- Lemma 85.3.5 (12): `g_n⁻¹` associates to a sheaf `F` on `C_total` the sheaf `F_n`
on `C_n` in case B. -/
@[stacks 09WG]
def fiberMorphism_inverseImage_iso_fiberRestrict (n : SimplexCategory) :
    (fiberMorphism F J n)⁻¹ ≅ fiberRestrict F J (Type w) n :=
  CategoryTheory.eqToIso (fiberMorphism_inverseImage F J n) ≪≫ fiberInverseImageIso F J n

/-- The case B inverse-image comparison is `eqToIso` of `fiberMorphism_inverseImage` composed
with `fiberInverseImageIso`. -/
theorem fiberMorphism_inverseImage_iso_fiberRestrict_eq (n : SimplexCategory) :
    fiberMorphism_inverseImage_iso_fiberRestrict F J n =
      CategoryTheory.eqToIso (fiberMorphism_inverseImage F J n) ≪≫
        fiberInverseImageIso F J n :=
  sorry

/-- Lemma 85.3.5 (13): `g_n⁻¹ : Sh(C_total) ⥤ Sh(C_n)` has a left adjoint `g^{Sh}_{n!}`
in case B. -/
@[stacks 09WG, instance]
instance fiberRestrict_isRightAdjoint (n : SimplexCategory) :
    (fiberRestrict F J (Type w) n).IsRightAdjoint :=
  (fiberSheafLowerShriek_adjunction F J n).isRightAdjoint

/-- Lemma 85.3.5 (14): for `G` in `Sh(C_n)` the restriction of `g^{Sh}_{n!} G` to `C_m`
is `∐_{φ : n ⟶ m} f_φ⁻¹ G` in case B. -/
@[stacks 09WG]
def fiberSheafLowerShriek_componentCoproduct (n m : SimplexCategory)
    [HasColimitsOfShape (Discrete (n ⟶ m))
      (Sheaf ((J (op m)).toGrothendieck) (Type w))]
    (G : Sheaf ((J (op n)).toGrothendieck) (Type w)) :
    (fiberRestrict F J (Type w) m).obj ((fiberSheafLowerShriek F J n).obj G) ≅
      ∐ fun φ : n ⟶ m ↦
        ((F.map φ.op).toFunctor.sheafPullbackCocontinuous (Type w)
          (J (op m)).toGrothendieck (J (op n)).toGrothendieck).obj G :=
  (fiberSheafLowerShriek_componentCoproductIso F J n m G).symm

/-- The case B coproduct identification is the inverse of the fiber coproduct comparison iso. -/
theorem fiberSheafLowerShriek_componentCoproduct_eq (n m : SimplexCategory)
    [HasColimitsOfShape (Discrete (n ⟶ m))
      (Sheaf ((J (op m)).toGrothendieck) (Type w))]
    (G : Sheaf ((J (op n)).toGrothendieck) (Type w)) :
    fiberSheafLowerShriek_componentCoproduct F J n m G =
      (fiberSheafLowerShriek_componentCoproductIso F J n m G).symm :=
  sorry

/-- Lemma 85.3.5 (15): `g^{Sh}_{n!}` commutes with finite connected limits in case B. -/
@[stacks 09WG, instance]
instance fiberSheafLowerShriek_preservesFiniteConnectedLimits (n : SimplexCategory)
    [∀ P : (F.obj (op n))ᵒᵖ ⥤ Type w, (ι F (op n)).op.HasPointwiseLeftKanExtension P] :
    PreservesFiniteConnectedLimits (fiberSheafLowerShriek F J n) :=
  sorry

variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [HasWeakSheafify (topology F J) AddCommGrpCat.{w}]
variable [HasSheafify (topology F J) AddCommGrpCat.{w}]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ AddCommGrpCat.{w},
    (ι F (op n)).op.HasLeftKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (F.obj (op n))ᵒᵖ ⥤ AddCommGrpCat.{w}),
    ((F.map φ.op).toFunctor).op.HasPointwiseRightKanExtension P]

/-- Lemma 85.3.5 (16): `g_n⁻¹ : Ab(C_total) ⥤ Ab(C_n)` has a left adjoint `g_{n!}`
in case B. -/
@[stacks 09WG, instance]
instance abelianFiberRestrict_isRightAdjoint (n : SimplexCategory) :
    (fiberRestrict F J AddCommGrpCat.{w} n).IsRightAdjoint :=
  (fiberAbelianLowerShriek_adjunction F J n).isRightAdjoint

/-- Lemma 85.3.5 (17): for `G` in `Ab(C_n)` the restriction of `g_{n!} G` to `C_m`
is `⊕_{φ : n ⟶ m} f_φ⁻¹ G` in case B. -/
@[stacks 09WG]
def fiberAbelianLowerShriek_componentBiproduct (n m : SimplexCategory)
    [HasColimitsOfShape (Discrete (n ⟶ m))
      (Sheaf ((J (op m)).toGrothendieck) AddCommGrpCat.{w})]
    (G : Sheaf ((J (op n)).toGrothendieck) AddCommGrpCat.{w}) :
    (fiberRestrict F J AddCommGrpCat.{w} m).obj ((fiberAbelianLowerShriek F J n).obj G) ≅
      ∐ fun φ : n ⟶ m ↦
        ((F.map φ.op).toFunctor.sheafPullbackCocontinuous AddCommGrpCat.{w}
          (J (op m)).toGrothendieck (J (op n)).toGrothendieck).obj G :=
  (fiberAbelianLowerShriek_componentBiproductIso F J n m G).symm

/-- The case B abelian identification is the inverse of the fiber biproduct comparison iso. -/
theorem fiberAbelianLowerShriek_componentBiproduct_eq (n m : SimplexCategory)
    [HasColimitsOfShape (Discrete (n ⟶ m))
      (Sheaf ((J (op m)).toGrothendieck) AddCommGrpCat.{w})]
    (G : Sheaf ((J (op n)).toGrothendieck) AddCommGrpCat.{w}) :
    fiberAbelianLowerShriek_componentBiproduct F J n m G =
      (fiberAbelianLowerShriek_componentBiproductIso F J n m G).symm :=
  sorry

/-- Lemma 85.3.5 (18): `g_{n!}` is exact in case B. -/
@[stacks 09WG]
theorem fiberAbelianLowerShriek_exact (n : SimplexCategory)
    [∀ P : (F.obj (op n))ᵒᵖ ⥤ AddCommGrpCat.{w},
      (ι F (op n)).op.HasPointwiseLeftKanExtension P] :
    exactFunctor
      (Sheaf ((J (op n)).toGrothendieck) AddCommGrpCat.{w})
      (Sheaf (topology F J) AddCommGrpCat.{w})
      (fiberAbelianLowerShriek F J n) :=
  sorry

end CategoryTheory.Grothendieck
