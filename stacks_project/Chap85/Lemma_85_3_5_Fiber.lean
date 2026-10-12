/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Sites.Pullback
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.LowerShriek
public import ReasLib.CategoryTheory.Sites.Pullback.FiniteConnectedLimits
public import ReasLib.CategoryTheory.Sites.Topos.Cocontinuous
public import stacks_project.Chap85.Situation_85_3_3_Fiberwise

/-!
# Fiber inclusion of a simplicial object of sites

The degree-`n` inclusion `Grothendieck.ι F (op n) : C_n ⥤ C_total` in case B of
Situation 85.3.3, the associated morphism of topoi `g_n`, restriction `F ↦ F_n`,
and the type-valued and abelian lower-shriek functors, together with the
componentwise coproduct/direct-sum formula.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Functor
open scoped CategoryTheory.MorphismOfTopoiIn

noncomputable section

universe u v w

namespace CategoryTheory.Grothendieck

variable (F : SimplicialObject Cat.{v, u}) (J : ∀ n, Precoverage (F.obj n))

/-- The morphism of topoi `g_n : Sh(C_n) ⟶ Sh(C_total)` associated to the fiber inclusion
`ι F (op n)`. -/
def fiberMorphism (n : SimplexCategory)
    [(ι F (op n)).IsCocontinuous (J (op n)).toGrothendieck (topology F J)]
    [HasSheafify (J (op n)).toGrothendieck (Type w)]
    [∀ P : (F.obj (op n))ᵒᵖ ⥤ Type w, (ι F (op n)).op.HasPointwiseRightKanExtension P] :
    MorphismOfTopoiIn (topology F J) (J (op n)).toGrothendieck :=
  (ι F (op n)).morphismOfTopoiInOfCocontinuous (J (op n)).toGrothendieck (topology F J)

/-- Inverse image of `g_n` is the sheafified cocontinuous pullback along `ι F (op n)`. -/
theorem fiberMorphism_inverseImage (n : SimplexCategory)
    [(ι F (op n)).IsCocontinuous (J (op n)).toGrothendieck (topology F J)]
    [HasSheafify (J (op n)).toGrothendieck (Type w)]
    [∀ P : (F.obj (op n))ᵒᵖ ⥤ Type w, (ι F (op n)).op.HasPointwiseRightKanExtension P] :
    (fiberMorphism F J n)⁻¹ =
      (ι F (op n)).sheafPullbackCocontinuous (Type w)
        (J (op n)).toGrothendieck (topology F J) :=
  sorry

/-- Restriction of sheaves along the degree-`n` fiber inclusion, i.e. `F ↦ F_n`. -/
abbrev fiberRestrict (A : Type (w + 1)) [Category.{w} A] (n : SimplexCategory)
    [(ι F (op n)).IsContinuous (J (op n)).toGrothendieck (topology F J)] :
    Sheaf (topology F J) A ⥤ Sheaf ((J (op n)).toGrothendieck) A :=
  (ι F (op n)).sheafPushforwardContinuous A (J (op n)).toGrothendieck (topology F J)

/-- `fiberRestrict` is continuous sheaf pushforward along `ι F (op n)`. -/
theorem fiberRestrict_eq (A : Type (w + 1)) [Category.{w} A] (n : SimplexCategory)
    [(ι F (op n)).IsContinuous (J (op n)).toGrothendieck (topology F J)] :
    fiberRestrict F J A n =
      (ι F (op n)).sheafPushforwardContinuous A (J (op n)).toGrothendieck (topology F J) :=
  sorry

/-- Type-valued lower shriek `g^{Sh}_{n!}` along the degree-`n` fiber inclusion. -/
abbrev fiberSheafLowerShriek (n : SimplexCategory)
    [(ι F (op n)).IsContinuous (J (op n)).toGrothendieck (topology F J)]
    [HasWeakSheafify (topology F J) (Type w)]
    [∀ P : (F.obj (op n))ᵒᵖ ⥤ Type w, (ι F (op n)).op.HasLeftKanExtension P] :
    Sheaf ((J (op n)).toGrothendieck) (Type w) ⥤ Sheaf (topology F J) (Type w) :=
  (ι F (op n)).sheafPullback (Type w) (J (op n)).toGrothendieck (topology F J)

/-- Abelian lower shriek `g_{n!}` along the degree-`n` fiber inclusion. -/
abbrev fiberAbelianLowerShriek (n : SimplexCategory)
    [(ι F (op n)).IsContinuous (J (op n)).toGrothendieck (topology F J)]
    [HasWeakSheafify (topology F J) AddCommGrpCat.{w}]
    [∀ P : (F.obj (op n))ᵒᵖ ⥤ AddCommGrpCat.{w}, (ι F (op n)).op.HasLeftKanExtension P] :
    Sheaf ((J (op n)).toGrothendieck) AddCommGrpCat.{w} ⥤
      Sheaf (topology F J) AddCommGrpCat.{w} :=
  (ι F (op n)).sheafPullback AddCommGrpCat.{w} (J (op n)).toGrothendieck (topology F J)

/-- The canonical cocontinuous-to-continuous comparison along `ι F (op n)`. -/
def fiberInverseImageIso (n : SimplexCategory)
    [(ι F (op n)).IsContinuous (J (op n)).toGrothendieck (topology F J)]
    [(ι F (op n)).IsCocontinuous (J (op n)).toGrothendieck (topology F J)]
    [HasWeakSheafify (J (op n)).toGrothendieck (Type w)]
    [HasWeakSheafify (topology F J) (Type w)]
    [∀ P : (F.obj (op n))ᵒᵖ ⥤ Type w, (ι F (op n)).op.HasPointwiseRightKanExtension P] :
    (ι F (op n)).sheafPullbackCocontinuous (Type w)
        (J (op n)).toGrothendieck (topology F J) ≅
      fiberRestrict F J (Type w) n :=
  asIso (Functor.CocontinuousPullback.comparison (ι F (op n))
    (J (op n)).toGrothendieck (topology F J))

/-- `fiberSheafLowerShriek` is sheaf pullback along `ι F (op n)`. -/
theorem fiberSheafLowerShriek_eq (n : SimplexCategory)
    [(ι F (op n)).IsContinuous (J (op n)).toGrothendieck (topology F J)]
    [HasWeakSheafify (topology F J) (Type w)]
    [∀ P : (F.obj (op n))ᵒᵖ ⥤ Type w, (ι F (op n)).op.HasLeftKanExtension P] :
    fiberSheafLowerShriek F J n =
      (ι F (op n)).sheafPullback (Type w) (J (op n)).toGrothendieck (topology F J) :=
  sorry

/-- `fiberAbelianLowerShriek` is sheaf pullback of abelian sheaves along `ι F (op n)`. -/
theorem fiberAbelianLowerShriek_eq (n : SimplexCategory)
    [(ι F (op n)).IsContinuous (J (op n)).toGrothendieck (topology F J)]
    [HasWeakSheafify (topology F J) AddCommGrpCat.{w}]
    [∀ P : (F.obj (op n))ᵒᵖ ⥤ AddCommGrpCat.{w}, (ι F (op n)).op.HasLeftKanExtension P] :
    fiberAbelianLowerShriek F J n =
      (ι F (op n)).sheafPullback AddCommGrpCat.{w}
        (J (op n)).toGrothendieck (topology F J) :=
  sorry

/-- The forward map of `fiberInverseImageIso` is the canonical comparison. -/
theorem fiberInverseImageIso_hom (n : SimplexCategory)
    [(ι F (op n)).IsContinuous (J (op n)).toGrothendieck (topology F J)]
    [(ι F (op n)).IsCocontinuous (J (op n)).toGrothendieck (topology F J)]
    [HasWeakSheafify (J (op n)).toGrothendieck (Type w)]
    [HasWeakSheafify (topology F J) (Type w)]
    [∀ P : (F.obj (op n))ᵒᵖ ⥤ Type w, (ι F (op n)).op.HasPointwiseRightKanExtension P] :
    (fiberInverseImageIso F J n).hom =
      Functor.CocontinuousPullback.comparison (ι F (op n))
        (J (op n)).toGrothendieck (topology F J) :=
  sorry

/-- Type-valued lower shriek is left adjoint to restriction along `ι F (op n)`. -/
def fiberSheafLowerShriek_adjunction (n : SimplexCategory)
    [(ι F (op n)).IsContinuous (J (op n)).toGrothendieck (topology F J)]
    [HasWeakSheafify (topology F J) (Type w)]
    [∀ P : (F.obj (op n))ᵒᵖ ⥤ Type w, (ι F (op n)).op.HasLeftKanExtension P] :
    fiberSheafLowerShriek F J n ⊣ fiberRestrict F J (Type w) n :=
  (ι F (op n)).sheafAdjunctionContinuous (Type w)
    (J (op n)).toGrothendieck (topology F J)

/-- Abelian lower shriek is left adjoint to restriction along `ι F (op n)`. -/
def fiberAbelianLowerShriek_adjunction (n : SimplexCategory)
    [(ι F (op n)).IsContinuous (J (op n)).toGrothendieck (topology F J)]
    [HasWeakSheafify (topology F J) AddCommGrpCat.{w}]
    [∀ P : (F.obj (op n))ᵒᵖ ⥤ AddCommGrpCat.{w}, (ι F (op n)).op.HasLeftKanExtension P] :
    fiberAbelianLowerShriek F J n ⊣ fiberRestrict F J AddCommGrpCat.{w} n :=
  (ι F (op n)).sheafAdjunctionContinuous AddCommGrpCat.{w}
    (J (op n)).toGrothendieck (topology F J)

/-- The type-valued fiber adjunction is continuous sheaf adjunction along `ι F (op n)`. -/
theorem fiberSheafLowerShriek_adjunction_eq (n : SimplexCategory)
    [(ι F (op n)).IsContinuous (J (op n)).toGrothendieck (topology F J)]
    [HasWeakSheafify (topology F J) (Type w)]
    [∀ P : (F.obj (op n))ᵒᵖ ⥤ Type w, (ι F (op n)).op.HasLeftKanExtension P] :
    fiberSheafLowerShriek_adjunction F J n =
      (ι F (op n)).sheafAdjunctionContinuous (Type w)
        (J (op n)).toGrothendieck (topology F J) :=
  sorry

/-- The abelian fiber adjunction is continuous sheaf adjunction along `ι F (op n)`. -/
theorem fiberAbelianLowerShriek_adjunction_eq (n : SimplexCategory)
    [(ι F (op n)).IsContinuous (J (op n)).toGrothendieck (topology F J)]
    [HasWeakSheafify (topology F J) AddCommGrpCat.{w}]
    [∀ P : (F.obj (op n))ᵒᵖ ⥤ AddCommGrpCat.{w}, (ι F (op n)).op.HasLeftKanExtension P] :
    fiberAbelianLowerShriek_adjunction F J n =
      (ι F (op n)).sheafAdjunctionContinuous AddCommGrpCat.{w}
        (J (op n)).toGrothendieck (topology F J) :=
  sorry

variable [IsFiberwiseSite F J]
variable [∀ n, (ι F (op n)).IsContinuous (J (op n)).toGrothendieck (topology F J)]
variable [∀ n, (ι F (op n)).IsCocontinuous (J (op n)).toGrothendieck (topology F J)]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [HasWeakSheafify (topology F J) (Type w)]
variable [∀ n, HasSheafify (J n).toGrothendieck (Type w)]
variable [∀ n, ∀ P : (F.obj n)ᵒᵖ ⥤ Type w, (ι F n).op.HasPointwiseRightKanExtension P]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ Type w, (ι F (op n)).op.HasLeftKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (F.obj (op n))ᵒᵖ ⥤ Type w),
    ((F.map φ.op).toFunctor).op.HasPointwiseRightKanExtension P]

/-- Inverse image `f_φ⁻¹` of type-valued sheaves along a simplex operator in case B. -/
abbrev fiberFacePullback {n m : SimplexCategory} (φ : n ⟶ m) :
    Sheaf ((J (op n)).toGrothendieck) (Type w) ⥤
      Sheaf ((J (op m)).toGrothendieck) (Type w) :=
  (F.map φ.op).toFunctor.sheafPullbackCocontinuous (Type w)
    (J (op m)).toGrothendieck (J (op n)).toGrothendieck

/-- `fiberFacePullback φ` is cocontinuous sheaf pullback along `u_φ`. -/
theorem fiberFacePullback_eq {n m : SimplexCategory} (φ : n ⟶ m) :
    fiberFacePullback F J φ =
      (F.map φ.op).toFunctor.sheafPullbackCocontinuous (Type w)
        (J (op m)).toGrothendieck (J (op n)).toGrothendieck :=
  sorry

/-- The canonical component map `f_φ⁻¹ G ⟶ (g^{Sh}_{n!} G)_m` in case B. -/
def fiberSheafLowerShriek_component {n m : SimplexCategory} (φ : n ⟶ m)
    (G : Sheaf ((J (op n)).toGrothendieck) (Type w)) :
    ((F.map φ.op).toFunctor.sheafPullbackCocontinuous (Type w)
      (J (op m)).toGrothendieck (J (op n)).toGrothendieck).obj G ⟶
      (fiberRestrict F J (Type w) m).obj ((fiberSheafLowerShriek F J n).obj G) :=
  (presheafToSheaf ((J (op m)).toGrothendieck) (Type w)).map
      (whiskerLeft (F.map φ.op).toFunctor.op
        ((sheafToPresheaf ((J (op n)).toGrothendieck) (Type w)).map
          ((fiberSheafLowerShriek_adjunction F J n).unit.app G))) ≫
    (presheafToSheaf ((J (op m)).toGrothendieck) (Type w)).map
      (whiskerRight (NatTrans.op (ιNatTrans φ.op))
        (((fiberSheafLowerShriek F J n).obj G).obj)) ≫
    (sheafificationAdjunction ((J (op m)).toGrothendieck) (Type w)).counit.app
      ((fiberRestrict F J (Type w) m).obj ((fiberSheafLowerShriek F J n).obj G))

/-- The coproduct comparison morphism
`∐_{φ : n ⟶ m} f_φ⁻¹ G ⟶ (g^{Sh}_{n!} G)_m` in case B. -/
def fiberSheafLowerShriek_componentCoproductHom (n m : SimplexCategory)
    [HasColimitsOfShape (Discrete (n ⟶ m))
      (Sheaf ((J (op m)).toGrothendieck) (Type w))]
    (G : Sheaf ((J (op n)).toGrothendieck) (Type w)) :
    (∐ fun φ : n ⟶ m =>
      ((F.map φ.op).toFunctor.sheafPullbackCocontinuous (Type w)
        (J (op m)).toGrothendieck (J (op n)).toGrothendieck).obj G) ⟶
      (fiberRestrict F J (Type w) m).obj ((fiberSheafLowerShriek F J n).obj G) :=
  Sigma.desc fun φ => fiberSheafLowerShriek_component F J φ G

/-- The case B coproduct comparison is the coproduct of the component maps. -/
theorem fiberSheafLowerShriek_componentCoproductHom_eq (n m : SimplexCategory)
    [HasColimitsOfShape (Discrete (n ⟶ m))
      (Sheaf ((J (op m)).toGrothendieck) (Type w))]
    (G : Sheaf ((J (op n)).toGrothendieck) (Type w)) :
    fiberSheafLowerShriek_componentCoproductHom F J n m G =
      Sigma.desc fun φ => fiberSheafLowerShriek_component F J φ G :=
  sorry

/-- The case B coproduct comparison morphism is an isomorphism. -/
instance fiberSheafLowerShriek_componentCoproductHom_isIso (n m : SimplexCategory)
    [HasColimitsOfShape (Discrete (n ⟶ m))
      (Sheaf ((J (op m)).toGrothendieck) (Type w))]
    (G : Sheaf ((J (op n)).toGrothendieck) (Type w)) :
    IsIso (fiberSheafLowerShriek_componentCoproductHom F J n m G) :=
  sorry

/-- Restriction of `g^{Sh}_{n!} G` to `C_m` is `∐_{φ : n ⟶ m} f_φ⁻¹ G` in case B. -/
def fiberSheafLowerShriek_componentCoproductIso (n m : SimplexCategory)
    [HasColimitsOfShape (Discrete (n ⟶ m))
      (Sheaf ((J (op m)).toGrothendieck) (Type w))]
    (G : Sheaf ((J (op n)).toGrothendieck) (Type w)) :
    (∐ fun φ : n ⟶ m =>
      ((F.map φ.op).toFunctor.sheafPullbackCocontinuous (Type w)
        (J (op m)).toGrothendieck (J (op n)).toGrothendieck).obj G) ≅
      (fiberRestrict F J (Type w) m).obj ((fiberSheafLowerShriek F J n).obj G) :=
  asIso (fiberSheafLowerShriek_componentCoproductHom F J n m G)

/-- The coproduct inclusion of `f_φ⁻¹ G` followed by the comparison is the component map. -/
theorem fiberSheafLowerShriek_componentCoproduct_ι (n m : SimplexCategory)
    [HasColimitsOfShape (Discrete (n ⟶ m))
      (Sheaf ((J (op m)).toGrothendieck) (Type w))]
    (G : Sheaf ((J (op n)).toGrothendieck) (Type w)) (φ : n ⟶ m) :
    Sigma.ι (fun ψ : n ⟶ m =>
        ((F.map ψ.op).toFunctor.sheafPullbackCocontinuous (Type w)
          (J (op m)).toGrothendieck (J (op n)).toGrothendieck).obj G) φ ≫
      (fiberSheafLowerShriek_componentCoproductIso F J n m G).hom =
      fiberSheafLowerShriek_component F J φ G :=
  sorry

variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [HasWeakSheafify (topology F J) AddCommGrpCat.{w}]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ AddCommGrpCat.{w},
    (ι F (op n)).op.HasLeftKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (F.obj (op n))ᵒᵖ ⥤ AddCommGrpCat.{w}),
    ((F.map φ.op).toFunctor).op.HasPointwiseRightKanExtension P]

/-- Inverse image `f_φ⁻¹` of abelian sheaves along a simplex operator in case B. -/
abbrev fiberAbelianFacePullback {n m : SimplexCategory} (φ : n ⟶ m) :
    Sheaf ((J (op n)).toGrothendieck) AddCommGrpCat.{w} ⥤
      Sheaf ((J (op m)).toGrothendieck) AddCommGrpCat.{w} :=
  (F.map φ.op).toFunctor.sheafPullbackCocontinuous AddCommGrpCat.{w}
    (J (op m)).toGrothendieck (J (op n)).toGrothendieck

/-- `fiberAbelianFacePullback φ` is cocontinuous sheaf pullback of abelian sheaves along `u_φ`. -/
theorem fiberAbelianFacePullback_eq {n m : SimplexCategory} (φ : n ⟶ m) :
    fiberAbelianFacePullback F J φ =
      (F.map φ.op).toFunctor.sheafPullbackCocontinuous AddCommGrpCat.{w}
        (J (op m)).toGrothendieck (J (op n)).toGrothendieck :=
  sorry

/-- The canonical component map `f_φ⁻¹ G ⟶ (g_{n!} G)_m` of abelian sheaves in case B. -/
def fiberAbelianLowerShriek_component {n m : SimplexCategory} (φ : n ⟶ m)
    (G : Sheaf ((J (op n)).toGrothendieck) AddCommGrpCat.{w}) :
    ((F.map φ.op).toFunctor.sheafPullbackCocontinuous AddCommGrpCat.{w}
      (J (op m)).toGrothendieck (J (op n)).toGrothendieck).obj G ⟶
      (fiberRestrict F J AddCommGrpCat.{w} m).obj
        ((fiberAbelianLowerShriek F J n).obj G) :=
  (presheafToSheaf ((J (op m)).toGrothendieck) AddCommGrpCat.{w}).map
      (whiskerLeft (F.map φ.op).toFunctor.op
        ((sheafToPresheaf ((J (op n)).toGrothendieck) AddCommGrpCat.{w}).map
          ((fiberAbelianLowerShriek_adjunction F J n).unit.app G))) ≫
    (presheafToSheaf ((J (op m)).toGrothendieck) AddCommGrpCat.{w}).map
      (whiskerRight (NatTrans.op (ιNatTrans φ.op))
        (((fiberAbelianLowerShriek F J n).obj G).obj)) ≫
    (sheafificationAdjunction ((J (op m)).toGrothendieck) AddCommGrpCat.{w}).counit.app
      ((fiberRestrict F J AddCommGrpCat.{w} m).obj
        ((fiberAbelianLowerShriek F J n).obj G))

/-- The direct-sum comparison morphism of abelian sheaves in case B. -/
def fiberAbelianLowerShriek_componentBiproductHom (n m : SimplexCategory)
    [HasColimitsOfShape (Discrete (n ⟶ m))
      (Sheaf ((J (op m)).toGrothendieck) AddCommGrpCat.{w})]
    (G : Sheaf ((J (op n)).toGrothendieck) AddCommGrpCat.{w}) :
    (∐ fun φ : n ⟶ m =>
      ((F.map φ.op).toFunctor.sheafPullbackCocontinuous AddCommGrpCat.{w}
        (J (op m)).toGrothendieck (J (op n)).toGrothendieck).obj G) ⟶
      (fiberRestrict F J AddCommGrpCat.{w} m).obj
        ((fiberAbelianLowerShriek F J n).obj G) :=
  Sigma.desc fun φ => fiberAbelianLowerShriek_component F J φ G

/-- The case B abelian comparison is the coproduct of the abelian component maps. -/
theorem fiberAbelianLowerShriek_componentBiproductHom_eq (n m : SimplexCategory)
    [HasColimitsOfShape (Discrete (n ⟶ m))
      (Sheaf ((J (op m)).toGrothendieck) AddCommGrpCat.{w})]
    (G : Sheaf ((J (op n)).toGrothendieck) AddCommGrpCat.{w}) :
    fiberAbelianLowerShriek_componentBiproductHom F J n m G =
      Sigma.desc fun φ => fiberAbelianLowerShriek_component F J φ G :=
  sorry

/-- The case B abelian direct-sum comparison morphism is an isomorphism. -/
instance fiberAbelianLowerShriek_componentBiproductHom_isIso (n m : SimplexCategory)
    [HasColimitsOfShape (Discrete (n ⟶ m))
      (Sheaf ((J (op m)).toGrothendieck) AddCommGrpCat.{w})]
    (G : Sheaf ((J (op n)).toGrothendieck) AddCommGrpCat.{w}) :
    IsIso (fiberAbelianLowerShriek_componentBiproductHom F J n m G) :=
  sorry

/-- Restriction of `g_{n!} G` to `C_m` is `⊕_{φ : n ⟶ m} f_φ⁻¹ G` in case B. -/
def fiberAbelianLowerShriek_componentBiproductIso (n m : SimplexCategory)
    [HasColimitsOfShape (Discrete (n ⟶ m))
      (Sheaf ((J (op m)).toGrothendieck) AddCommGrpCat.{w})]
    (G : Sheaf ((J (op n)).toGrothendieck) AddCommGrpCat.{w}) :
    (∐ fun φ : n ⟶ m =>
      ((F.map φ.op).toFunctor.sheafPullbackCocontinuous AddCommGrpCat.{w}
        (J (op m)).toGrothendieck (J (op n)).toGrothendieck).obj G) ≅
      (fiberRestrict F J AddCommGrpCat.{w} m).obj
        ((fiberAbelianLowerShriek F J n).obj G) :=
  asIso (fiberAbelianLowerShriek_componentBiproductHom F J n m G)

/-- The direct-sum inclusion of `f_φ⁻¹ G` followed by the comparison is the component map. -/
theorem fiberAbelianLowerShriek_componentBiproduct_ι (n m : SimplexCategory)
    [HasColimitsOfShape (Discrete (n ⟶ m))
      (Sheaf ((J (op m)).toGrothendieck) AddCommGrpCat.{w})]
    (G : Sheaf ((J (op n)).toGrothendieck) AddCommGrpCat.{w}) (φ : n ⟶ m) :
    Sigma.ι (fun ψ : n ⟶ m =>
        ((F.map ψ.op).toFunctor.sheafPullbackCocontinuous AddCommGrpCat.{w}
          (J (op m)).toGrothendieck (J (op n)).toGrothendieck).obj G) φ ≫
      (fiberAbelianLowerShriek_componentBiproductIso F J n m G).hom =
      fiberAbelianLowerShriek_component F J φ G :=
  sorry

end CategoryTheory.Grothendieck
