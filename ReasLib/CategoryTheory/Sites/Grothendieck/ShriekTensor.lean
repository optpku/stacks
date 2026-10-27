/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Grothendieck.Cartesian
public import ReasLib.CategoryTheory.Sites.AbelianTensor
public import ReasLib.CategoryTheory.Sites.Monoidal.Continuous
public import ReasLib.Algebra.Homology.DerivedCategory.Adjunction

set_option backward.privateInPublic true

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Functor
open CategoryTheory.MonoidalCategory

noncomputable section

universe u v w

namespace CategoryTheory.Grothendieck.AbelianDerived

variable (C : SimplicialObject Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [IsFiberwiseSite C J]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [HasWeakSheafify (topology C J) (Type w)]
variable [∀ n, HasSheafify (J n).toGrothendieck (Type w)]
variable [HasSheafify (topology C J) (Type w)]
variable [∀ n, ∀ P : (C.obj (op n))ᵒᵖ ⥤ Type w,
    (ι C (op n)).op.HasLeftKanExtension P]
variable [∀ n, ∀ P : (C.obj (op n))ᵒᵖ ⥤ Type w,
    (ι C (op n)).op.HasPointwiseRightKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj (op n))ᵒᵖ ⥤ Type w),
    ((C.map φ.op).toFunctor).op.HasPointwiseRightKanExtension P]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [HasWeakSheafify (topology C J) AddCommGrpCat.{w}]
variable [HasSheafify (topology C J) AddCommGrpCat.{w}]
variable [∀ n, HasSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [∀ n, ∀ P : (C.obj (op n))ᵒᵖ ⥤ AddCommGrpCat.{w},
    (ι C (op n)).op.HasLeftKanExtension P]
variable [∀ n, ∀ P : (C.obj (op n))ᵒᵖ ⥤ AddCommGrpCat.{w},
    (ι C (op n)).op.HasPointwiseLeftKanExtension P]
variable [∀ n, ∀ P : (C.obj (op n))ᵒᵖ ⥤ AddCommGrpCat.{w},
    (ι C (op n)).op.HasPointwiseRightKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj (op n))ᵒᵖ ⥤ AddCommGrpCat.{w}),
    ((C.map φ.op).toFunctor).op.HasPointwiseRightKanExtension P]

/-- The exact functor extending abelian sheaves from one degree to the total site. -/
def lowerShriekExact (n : SimplexCategory) :
    Sheaf ((J (op n)).toGrothendieck) AddCommGrpCat.{w} ⥤ₑ
      Sheaf (topology C J) AddCommGrpCat.{w} :=
  ⟨fiberAbelianLowerShriek C J n, fiberAbelianLowerShriek_exact C J n⟩

/-- Exact lower shriek on unbounded derived categories of abelian sheaves. -/
def lowerShriek (n : SimplexCategory) :
    DerivedCategory (Sheaf ((J (op n)).toGrothendieck) AddCommGrpCat.{w}) ⥤
      DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w}) :=
  (lowerShriekExact C J n).mapDerivedCategory

/-- Exact lower shriek is left adjoint to derived restriction. -/
def lowerShriekAdjunction (n : SimplexCategory) :
    lowerShriek C J n ⊣ derivedRestrict C J n :=
  Adjunction.mapDerivedCategory (L := (lowerShriekExact C J n).obj)
    (fiberAbelianLowerShriek_adjunction C J n)

/-- Restriction to a degree preserves the canonical integer tensor. -/
instance restrictMonoidal (n : SimplexCategory) :
    (fiberRestrict C J AddCommGrpCat.{w} n).Monoidal :=
  (ι C (op n)).sheafPushforwardContinuousMonoidal

/-- Tensoring with the lower-shriek integer sheaf is exact. -/
theorem shriekIntegerTensor_exact (n : SimplexCategory) :
    exactFunctor (Sheaf (topology C J) AddCommGrpCat.{w})
      (Sheaf (topology C J) AddCommGrpCat.{w})
      (tensorLeft ((fiberAbelianLowerShriek C J n).obj
        (constantIntegerSheaf (J (op n)).toGrothendieck))) := sorry

/-- Exact tensoring with the lower-shriek integer sheaf. -/
def shriekIntegerTensorExact (n : SimplexCategory) :
    Sheaf (topology C J) AddCommGrpCat.{w} ⥤ₑ
      Sheaf (topology C J) AddCommGrpCat.{w} :=
  ⟨tensorLeft ((fiberAbelianLowerShriek C J n).obj
      (constantIntegerSheaf (J (op n)).toGrothendieck)), shriekIntegerTensor_exact C J n⟩

/-- Derived integer tensor with the flat lower-shriek integer sheaf. -/
def shriekIntegerTensor (n : SimplexCategory) :
    DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w}) ⥤
      DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w}) :=
  (shriekIntegerTensorExact C J n).mapDerivedCategory

/-- The restriction mate obtained by tensoring the adjunction unit at the integer sheaf. -/
def shriekTensorMate (n : SimplexCategory)
    (F : Sheaf (topology C J) AddCommGrpCat.{w}) :
    (fiberRestrict C J AddCommGrpCat.{w} n).obj F ⟶
      (fiberRestrict C J AddCommGrpCat.{w} n).obj
        ((fiberAbelianLowerShriek C J n).obj (constantIntegerSheaf (J (op n)).toGrothendieck) ⊗ F) :=
  (leftUnitor ((fiberRestrict C J AddCommGrpCat.{w} n).obj F)).inv ≫
    ((Sheaf.abelianTensorUnitIsoInteger (J (op n)).toGrothendieck).hom ⊗ₘ
      𝟙 ((fiberRestrict C J AddCommGrpCat.{w} n).obj F)) ≫
    ((fiberAbelianLowerShriek_adjunction C J n).unit.app
        (constantIntegerSheaf (J (op n)).toGrothendieck) ⊗ₘ
      𝟙 ((fiberRestrict C J AddCommGrpCat.{w} n).obj F)) ≫
    LaxMonoidal.μ (fiberRestrict C J AddCommGrpCat.{w} n)
      ((fiberAbelianLowerShriek C J n).obj (constantIntegerSheaf (J (op n)).toGrothendieck)) F

/-- The lower-shriek tensor comparison is the adjunct of the unit-tensor mate. -/
def shriekTensorHom (n : SimplexCategory)
    (F : Sheaf (topology C J) AddCommGrpCat.{w}) :
    (fiberAbelianLowerShriek C J n).obj ((fiberRestrict C J AddCommGrpCat.{w} n).obj F) ⟶
      (fiberAbelianLowerShriek C J n).obj (constantIntegerSheaf (J (op n)).toGrothendieck) ⊗ F :=
  ((fiberAbelianLowerShriek_adjunction C J n).homEquiv _ _).symm (shriekTensorMate C J n F)

/-- The unit-tensor mates form a natural transformation on abelian sheaves. -/
def shriekTensorMateNatTrans (n : SimplexCategory) :
    fiberRestrict C J AddCommGrpCat.{w} n ⟶
      (shriekIntegerTensorExact C J n).obj ⋙ fiberRestrict C J AddCommGrpCat.{w} n where
  app F := shriekTensorMate C J n F
  naturality := sorry

/-- The adjunct tensor comparisons form a natural transformation on abelian sheaves. -/
def shriekTensorNatTrans (n : SimplexCategory) :
    fiberRestrict C J AddCommGrpCat.{w} n ⋙ fiberAbelianLowerShriek C J n ⟶
      (shriekIntegerTensorExact C J n).obj where
  app F := shriekTensorHom C J n F
  naturality := sorry

/-- Derived restriction followed by lower shriek agrees with deriving their composite. -/
private def shriekCompIso (n : SimplexCategory) :
    ((derivedComponentExact C J n).comp (lowerShriekExact C J n)).mapDerivedCategory ≅
      derivedRestrict C J n ⋙ lowerShriek C J n :=
  ExactFunctor.MapDerivedCategory.compFunctorIso
    (derivedComponentExact C J n) (lowerShriekExact C J n)

/-- The canonical comparison from the lower shriek of a restriction to derived integer tensor. -/
def shriekTensorComparison (n : SimplexCategory)
    (K : DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w})) :
    (lowerShriek C J n).obj ((derivedRestrict C J n).obj K) ⟶
      (shriekIntegerTensor C J n).obj K :=
  (shriekCompIso C J n).inv.app K ≫
    (ExactFunctor.MapDerivedCategory.map
      (F := (derivedComponentExact C J n).comp (lowerShriekExact C J n))
      (G := shriekIntegerTensorExact C J n)
      (ObjectProperty.homMk (shriekTensorNatTrans C J n))).app K

/-- The canonical unit-tensor mate on derived abelian sheaves, obtained by localization. -/
def shriekTensorDerivedMate (n : SimplexCategory)
    (K : DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w})) :
    (derivedRestrict C J n).obj K ⟶
      (derivedRestrict C J n).obj ((shriekIntegerTensor C J n).obj K) :=
  (ExactFunctor.MapDerivedCategory.map
      (F := derivedComponentExact C J n)
      (G := (shriekIntegerTensorExact C J n).comp (derivedComponentExact C J n))
      (ObjectProperty.homMk (shriekTensorMateNatTrans C J n))).app K ≫
    (ExactFunctor.MapDerivedCategory.compFunctorIso
      (shriekIntegerTensorExact C J n) (derivedComponentExact C J n)).hom.app K

/-- The derived tensor comparison is the adjunct of its localized unit-tensor mate. -/
theorem shriekTensorComparison_spec (n : SimplexCategory)
    (K : DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w})) :
    shriekTensorComparison C J n K =
      ((lowerShriekAdjunction C J n).homEquiv
        ((derivedRestrict C J n).obj K) ((shriekIntegerTensor C J n).obj K)).symm
        (shriekTensorDerivedMate C J n K) := sorry

/-- A derived abelian sheaf is cartesian exactly when every canonical shriek-tensor
comparison is invertible. -/
theorem isCartesian_iff_shriekTensor
    (K : DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w})) :
    IsCartesian C J K ↔ ∀ n : SimplexCategory, IsIso (shriekTensorComparison C J n K) := sorry

end CategoryTheory.Grothendieck.AbelianDerived
