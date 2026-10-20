module

public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import ReasLib.CategoryTheory.Limits.FiniteConnected.Preserves
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Sites.Pullback
public import ReasLib.CategoryTheory.Sites.Topos.Cocontinuous
public import ReasLib.CategoryTheory.Sites.Grothendieck.SimplicialTopos

/-!
# Fiber restriction, lower shriek, and component comparisons
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.MorphismOfTopoiIn

noncomputable section

universe u v w

open Functor

namespace CategoryTheory.Grothendieck

variable (F : SimplicialObject Cat.{v, u}) (J : ∀ n, Precoverage (F.obj n))

/-- Fiber inclusions of a fiberwise simplicial site are continuous. -/
instance fiberInclusion_isContinuous [IsFiberwiseSite F J] (n : SimplexCategory) :
    (ι F (op n)).IsContinuous (J (op n)).toGrothendieck (topology F J) :=
  HasSheafTransitions.component_continuous (F := F) (J := J) n

/-- Fiber inclusions of a fiberwise simplicial site are cocontinuous. -/
instance fiberInclusion_isCocontinuous [IsFiberwiseSite F J] (n : SimplexCategory) :
    (ι F (op n)).IsCocontinuous (J (op n)).toGrothendieck (topology F J) :=
  HasSheafTransitions.component_cocontinuous (F := F) (J := J) n

end CategoryTheory.Grothendieck

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
  rfl

/-- Restriction of sheaves along the degree-`n` fiber inclusion, i.e. `F ↦ F_n`. -/
abbrev fiberRestrict (A : Type (w + 1)) [Category.{w} A] (n : SimplexCategory)
    [(ι F (op n)).IsContinuous (J (op n)).toGrothendieck (topology F J)] :
    Sheaf (topology F J) A ⥤ Sheaf ((J (op n)).toGrothendieck) A :=
  (ι F (op n)).sheafPushforwardContinuous A (J (op n)).toGrothendieck (topology F J)

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
  Functor.CocontinuousPullback.comparisonIso (ι F (op n))
    (J (op n)).toGrothendieck (topology F J)

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
  rfl

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

variable [IsFiberwiseSite F J]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [HasWeakSheafify (topology F J) (Type w)]
variable [∀ n, HasSheafify (J n).toGrothendieck (Type w)]
variable [∀ n, ∀ P : (F.obj n)ᵒᵖ ⥤ Type w, (ι F n).op.HasPointwiseRightKanExtension P]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ Type w, (ι F (op n)).op.HasLeftKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (F.obj (op n))ᵒᵖ ⥤ Type w),
    ((F.map φ.op).toFunctor).op.HasPointwiseRightKanExtension P]

/-- The canonical component map `f_φ⁻¹ G ⟶ (g^{Sh}_{n!} G)_m`. -/
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
`∐_{φ : n ⟶ m} f_φ⁻¹ G ⟶ (g^{Sh}_{n!} G)_m`. -/
def fiberSheafLowerShriek_componentCoproductHom (n m : SimplexCategory)
    [HasColimitsOfShape (Discrete (n ⟶ m))
      (Sheaf ((J (op m)).toGrothendieck) (Type w))]
    (G : Sheaf ((J (op n)).toGrothendieck) (Type w)) :
    (∐ fun φ : n ⟶ m =>
      ((F.map φ.op).toFunctor.sheafPullbackCocontinuous (Type w)
        (J (op m)).toGrothendieck (J (op n)).toGrothendieck).obj G) ⟶
      (fiberRestrict F J (Type w) m).obj ((fiberSheafLowerShriek F J n).obj G) :=
  Sigma.desc fun φ => fiberSheafLowerShriek_component F J φ G

/-- The coproduct comparison morphism is an isomorphism. -/
instance fiberSheafLowerShriek_componentCoproductHom_isIso (n m : SimplexCategory)
    [HasColimitsOfShape (Discrete (n ⟶ m))
      (Sheaf ((J (op m)).toGrothendieck) (Type w))]
    (G : Sheaf ((J (op n)).toGrothendieck) (Type w)) :
    IsIso (fiberSheafLowerShriek_componentCoproductHom F J n m G) :=
  sorry

/-- The coproduct inclusion of `f_φ⁻¹ G` followed by the comparison is the component map. -/
theorem fiberSheafLowerShriek_componentCoproduct_ι (n m : SimplexCategory)
    [HasColimitsOfShape (Discrete (n ⟶ m))
      (Sheaf ((J (op m)).toGrothendieck) (Type w))]
    (G : Sheaf ((J (op n)).toGrothendieck) (Type w)) (φ : n ⟶ m) :
    Sigma.ι (fun ψ : n ⟶ m =>
        ((F.map ψ.op).toFunctor.sheafPullbackCocontinuous (Type w)
          (J (op m)).toGrothendieck (J (op n)).toGrothendieck).obj G) φ ≫
      fiberSheafLowerShriek_componentCoproductHom F J n m G =
      fiberSheafLowerShriek_component F J φ G :=
  by
    apply Sigma.ι_desc

variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [HasWeakSheafify (topology F J) AddCommGrpCat.{w}]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ AddCommGrpCat.{w},
    (ι F (op n)).op.HasLeftKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (F.obj (op n))ᵒᵖ ⥤ AddCommGrpCat.{w}),
    ((F.map φ.op).toFunctor).op.HasPointwiseRightKanExtension P]

/-- The canonical component map `f_φ⁻¹ G ⟶ (g_{n!} G)_m` of abelian sheaves. -/
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

/-- The direct-sum comparison morphism of abelian sheaves. -/
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

/-- The abelian direct-sum comparison morphism is an isomorphism. -/
instance fiberAbelianLowerShriek_componentBiproductHom_isIso (n m : SimplexCategory)
    [HasColimitsOfShape (Discrete (n ⟶ m))
      (Sheaf ((J (op m)).toGrothendieck) AddCommGrpCat.{w})]
    (G : Sheaf ((J (op n)).toGrothendieck) AddCommGrpCat.{w}) :
    IsIso (fiberAbelianLowerShriek_componentBiproductHom F J n m G) :=
  sorry

/-- The direct-sum inclusion of `f_φ⁻¹ G` followed by the comparison is the component map. -/
theorem fiberAbelianLowerShriek_componentBiproduct_ι (n m : SimplexCategory)
    [HasColimitsOfShape (Discrete (n ⟶ m))
      (Sheaf ((J (op m)).toGrothendieck) AddCommGrpCat.{w})]
    (G : Sheaf ((J (op n)).toGrothendieck) AddCommGrpCat.{w}) (φ : n ⟶ m) :
    Sigma.ι (fun ψ : n ⟶ m =>
        ((F.map ψ.op).toFunctor.sheafPullbackCocontinuous AddCommGrpCat.{w}
          (J (op m)).toGrothendieck (J (op n)).toGrothendieck).obj G) φ ≫
      fiberAbelianLowerShriek_componentBiproductHom F J n m G =
      fiberAbelianLowerShriek_component F J φ G :=
  by
    apply Sigma.ι_desc

end CategoryTheory.Grothendieck

namespace CategoryTheory.Grothendieck

variable (F : SimplicialObject Cat.{v, u}) (J : ∀ n, Precoverage (F.obj n))
variable [IsFiberwiseSite F J]

variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [HasWeakSheafify (topology F J) (Type w)]
variable [∀ n, HasSheafify (J n).toGrothendieck (Type w)]
variable [HasSheafify (topology F J) (Type w)]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ Type w, (ι F (op n)).op.HasLeftKanExtension P]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ Type w, (ι F (op n)).op.HasPointwiseRightKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (F.obj (op n))ᵒᵖ ⥤ Type w),
    ((F.map φ.op).toFunctor).op.HasPointwiseRightKanExtension P]

/-- The inverse image of the canonical fiber topos morphism is naturally isomorphic to restriction. -/
def fiberMorphism_inverseImage_iso_fiberRestrict (n : SimplexCategory) :
    (fiberMorphism F J n)⁻¹ ≅ fiberRestrict F J (Type w) n :=
  CategoryTheory.eqToIso (fiberMorphism_inverseImage F J n) ≪≫ fiberInverseImageIso F J n

/-- Type-valued fiber lower shriek preserves finite connected limits. -/
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

/-- Abelian fiber lower shriek preserves finite limits and finite colimits. -/
theorem fiberAbelianLowerShriek_exact (n : SimplexCategory)
    [∀ P : (F.obj (op n))ᵒᵖ ⥤ AddCommGrpCat.{w},
      (ι F (op n)).op.HasPointwiseLeftKanExtension P] :
    exactFunctor
      (Sheaf ((J (op n)).toGrothendieck) AddCommGrpCat.{w})
      (Sheaf (topology F J) AddCommGrpCat.{w})
      (fiberAbelianLowerShriek F J n) :=
  sorry

end CategoryTheory.Grothendieck
