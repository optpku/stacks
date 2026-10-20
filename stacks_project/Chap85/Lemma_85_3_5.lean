module

public import Mathlib.CategoryTheory.Limits.ExactFunctor
import StacksCheckRecall
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

variable (n : SimplexCategory)

namespace CategoryTheory.SimplicialSites

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [IsMorphismDiagram C J]

/- Lemma 85.3.5. Stage inclusions, restriction, and lower shriek in both simplicial-site presentations. -/
@[stacks 09WG] #check (CategoryTheory.SimplicialSites.ofStage_isContinuous :
  ∀ (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
    [IsSiteDiagram C J] (n : SimplexCategory),
    (ofStage C n).IsContinuous (J n).toGrothendieck (topology C J))

#check (CategoryTheory.SimplicialSites.ofStage_isCocontinuous C J :
  ∀ (n : SimplexCategory),
    (ofStage C n).IsCocontinuous (J n).toGrothendieck (topology C J))

variable [HasWeakSheafify (topology C J) (Type w)]
variable [∀ n, HasSheafify (J n).toGrothendieck (Type w)]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ Type w, (ofStage C n).op.HasLeftKanExtension P]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ Type w, (ofStage C n).op.HasPointwiseRightKanExtension P]
variable [HasSheafify (topology C J) (Type w)]

#check (CategoryTheory.SimplicialSites.ofStageMorphism_inverseImage_iso_stageRestrict C J :
  ∀ (n : SimplexCategory),
    (ofStageMorphism C J n)⁻¹ ≅ stageRestrict C J (Type w) n)

#check (CategoryTheory.SimplicialSites.sheafLowerShriek_adjunction C J n :
  sheafLowerShriek C J n ⊣ stageRestrict C J (Type w) n)

#check (CategoryTheory.SimplicialSites.sheafLowerShriek_componentCoproductHom_isIso C J :
  ∀ (n m : SimplexCategory)
    [HasColimitsOfShape (Discrete (n ⟶ m)) (Sheaf ((J m).toGrothendieck) (Type w))]
    (G : Sheaf ((J n).toGrothendieck) (Type w)),
    IsIso (sheafLowerShriek_componentCoproductHom C J n m G))

#check (CategoryTheory.SimplicialSites.sheafLowerShriek_preservesFiniteConnectedLimits C J :
  ∀ (n : SimplexCategory)
    [∀ P : (C.obj n)ᵒᵖ ⥤ Type w, (ofStage C n).op.HasPointwiseLeftKanExtension P],
    PreservesFiniteConnectedLimits (sheafLowerShriek C J n))

variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [HasWeakSheafify (topology C J) AddCommGrpCat.{w}]
variable [HasSheafify (topology C J) AddCommGrpCat.{w}]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ AddCommGrpCat.{w}, (ofStage C n).op.HasLeftKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ AddCommGrpCat.{w}),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]

#check (CategoryTheory.SimplicialSites.abelianLowerShriek_adjunction C J n :
  abelianLowerShriek C J n ⊣ stageRestrict C J AddCommGrpCat.{w} n)

#check (CategoryTheory.SimplicialSites.abelianLowerShriek_componentBiproductHom_isIso C J :
  ∀ (n m : SimplexCategory)
    [HasColimitsOfShape (Discrete (n ⟶ m))
      (Sheaf ((J m).toGrothendieck) AddCommGrpCat.{w})]
    (G : Sheaf ((J n).toGrothendieck) AddCommGrpCat.{w}),
    IsIso (abelianLowerShriek_componentBiproductHom C J n m G))

#check (CategoryTheory.SimplicialSites.abelianLowerShriek_exact C J :
  ∀ (n : SimplexCategory)
    [∀ P : (C.obj n)ᵒᵖ ⥤ AddCommGrpCat.{w},
      (ofStage C n).op.HasPointwiseLeftKanExtension P],
    exactFunctor
      (Sheaf ((J n).toGrothendieck) AddCommGrpCat.{w})
      (Sheaf (topology C J) AddCommGrpCat.{w})
      (abelianLowerShriek C J n))

end CategoryTheory.SimplicialSites

namespace CategoryTheory.Grothendieck

variable (F : SimplicialObject Cat.{v, u}) (J : ∀ n, Precoverage (F.obj n))
variable [IsFiberwiseSite F J]

#check (CategoryTheory.Grothendieck.fiberInclusion_isContinuous F J :
  ∀ (n : SimplexCategory),
    (ι F (op n)).IsContinuous (J (op n)).toGrothendieck (topology F J))

#check (CategoryTheory.Grothendieck.fiberInclusion_isCocontinuous F J :
  ∀ (n : SimplexCategory),
    (ι F (op n)).IsCocontinuous (J (op n)).toGrothendieck (topology F J))

variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [HasWeakSheafify (topology F J) (Type w)]
variable [∀ n, HasSheafify (J n).toGrothendieck (Type w)]
variable [HasSheafify (topology F J) (Type w)]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ Type w, (ι F (op n)).op.HasLeftKanExtension P]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ Type w, (ι F (op n)).op.HasPointwiseRightKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (F.obj (op n))ᵒᵖ ⥤ Type w),
    ((F.map φ.op).toFunctor).op.HasPointwiseRightKanExtension P]

#check (CategoryTheory.Grothendieck.fiberMorphism_inverseImage_iso_fiberRestrict F J :
  ∀ (n : SimplexCategory),
    (fiberMorphism F J n)⁻¹ ≅ fiberRestrict F J (Type w) n)

#check (CategoryTheory.Grothendieck.fiberSheafLowerShriek_adjunction F J n :
  fiberSheafLowerShriek F J n ⊣ fiberRestrict F J (Type w) n)

#check (CategoryTheory.Grothendieck.fiberSheafLowerShriek_componentCoproductHom_isIso F J :
  ∀ (n m : SimplexCategory)
    [HasColimitsOfShape (Discrete (n ⟶ m))
      (Sheaf ((J (op m)).toGrothendieck) (Type w))]
    (G : Sheaf ((J (op n)).toGrothendieck) (Type w)),
    IsIso (fiberSheafLowerShriek_componentCoproductHom F J n m G))

#check (CategoryTheory.Grothendieck.fiberSheafLowerShriek_preservesFiniteConnectedLimits F J :
  ∀ (n : SimplexCategory)
    [∀ P : (F.obj (op n))ᵒᵖ ⥤ Type w, (ι F (op n)).op.HasPointwiseLeftKanExtension P],
    PreservesFiniteConnectedLimits (fiberSheafLowerShriek F J n))

variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [HasWeakSheafify (topology F J) AddCommGrpCat.{w}]
variable [HasSheafify (topology F J) AddCommGrpCat.{w}]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ AddCommGrpCat.{w},
    (ι F (op n)).op.HasLeftKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (F.obj (op n))ᵒᵖ ⥤ AddCommGrpCat.{w}),
    ((F.map φ.op).toFunctor).op.HasPointwiseRightKanExtension P]

#check (CategoryTheory.Grothendieck.fiberAbelianLowerShriek_adjunction F J n :
  fiberAbelianLowerShriek F J n ⊣ fiberRestrict F J AddCommGrpCat.{w} n)

#check (CategoryTheory.Grothendieck.fiberAbelianLowerShriek_componentBiproductHom_isIso F J :
  ∀ (n m : SimplexCategory)
    [HasColimitsOfShape (Discrete (n ⟶ m))
      (Sheaf ((J (op m)).toGrothendieck) AddCommGrpCat.{w})]
    (G : Sheaf ((J (op n)).toGrothendieck) AddCommGrpCat.{w}),
    IsIso (fiberAbelianLowerShriek_componentBiproductHom F J n m G))

#check (CategoryTheory.Grothendieck.fiberAbelianLowerShriek_exact F J :
  ∀ (n : SimplexCategory)
    [∀ P : (F.obj (op n))ᵒᵖ ⥤ AddCommGrpCat.{w},
      (ι F (op n)).op.HasPointwiseLeftKanExtension P],
    exactFunctor
      (Sheaf ((J (op n)).toGrothendieck) AddCommGrpCat.{w})
      (Sheaf (topology F J) AddCommGrpCat.{w})
      (fiberAbelianLowerShriek F J n))

end CategoryTheory.Grothendieck
