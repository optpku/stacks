module

public import ReasLib.CategoryTheory.DerivedCategory.Limit.Sequential.Tower
import Mathlib.Tactic.CrossRefAttribute

/-!
# Stagewise evaluation of degree-zero inverse systems

The degree-zero embedding may be formed before or after evaluating a sequential inverse system.
This leaf owns the resulting tower isomorphism.  Its component maps are explicit; only their
naturality is proof data.
@stack 0D2L
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe wA wSys u v

namespace CategoryTheory.DerivedLimit.Stage

variable {A : Type u} [Category.{v} A] [Abelian A]
variable [HasDerivedCategory.{wA} A]
variable [HasDerivedCategory.{wSys} (SequentialInverseSystem A)]

/-- The stagewise comparison for a sequential-system object embedded in degree `q`. -/
@[stacks 0D2L "stage comparison in a fixed degree"]
noncomputable def singleTowerComponentIsoAt
    (M : SequentialInverseSystem A) (q : ℤ) (n : ℕ) :
    (tower
      ((DerivedCategory.singleFunctor (SequentialInverseSystem A) q).obj M)).obj
        (Opposite.op n) ≅
      (M ⋙ DerivedCategory.singleFunctor A q).obj (Opposite.op n) :=
  (((CategoryTheory.evaluation ℕᵒᵖ A).obj (Opposite.op n)).mapDerivedCategoryFactors.app
      ((CochainComplex.singleFunctor (SequentialInverseSystem A) q).obj M)) ≪≫
    DerivedCategory.Q.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex
        (((CategoryTheory.evaluation ℕᵒᵖ A).obj (Opposite.op n)) :
          SequentialInverseSystem A ⥤ A)
        (ComplexShape.up ℤ) q).app M) ≪≫
    (DerivedCategory.singleFunctorIsoCompQ A q).app (M.obj (Opposite.op n))

/-- Lemma 15.103.3 (0D2L): the degree-zero stage comparison used by the source statement. -/
@[stacks 0D2L "degree-zero stage comparison"]
noncomputable abbrev singleTowerComponentIso
    (M : SequentialInverseSystem A) (n : ℕ) :
    (tower
      ((DerivedCategory.singleFunctor (SequentialInverseSystem A) (0 : ℤ)).obj M)).obj
        (Opposite.op n) ≅
      (M ⋙ DerivedCategory.singleFunctor A (0 : ℤ)).obj (Opposite.op n) :=
  singleTowerComponentIsoAt M 0 n

/-- The stagewise degree-zero comparisons are natural in the index of the inverse system. -/
@[reassoc, stacks 0D2L "naturality of the degree-zero stage comparison"]
theorem singleTowerComponentIso_naturality
    (M : SequentialInverseSystem A) {m n : ℕᵒᵖ} (f : m ⟶ n) :
    (tower
        ((DerivedCategory.singleFunctor (SequentialInverseSystem A) (0 : ℤ)).obj M)).map f ≫
        (singleTowerComponentIso M (Opposite.unop n)).hom =
        (singleTowerComponentIso M (Opposite.unop m)).hom ≫
        (M ⋙ DerivedCategory.singleFunctor A (0 : ℤ)).map f := sorry

/-- Naturality of the stage comparison in an arbitrary fixed degree. -/
@[reassoc, stacks 0D2L "naturality of a fixed-degree stage comparison"]
theorem singleTowerComponentIsoAt_naturality
    (M : SequentialInverseSystem A) (q : ℤ) {m n : ℕᵒᵖ} (f : m ⟶ n) :
    (tower
        ((DerivedCategory.singleFunctor (SequentialInverseSystem A) q).obj M)).map f ≫
        (singleTowerComponentIsoAt M q (Opposite.unop n)).hom =
      (singleTowerComponentIsoAt M q (Opposite.unop m)).hom ≫
        (M ⋙ DerivedCategory.singleFunctor A q).map f := sorry

/-- Lemma 15.103.3 (0D2L): stagewise derived evaluation of a degree-zero inverse-system object is
canonically isomorphic to the tower obtained by embedding every stage in degree zero. -/
@[stacks 0D2L "stagewise tower of a degree-zero inverse system"]
noncomputable def singleTowerIso (M : SequentialInverseSystem A) :
    tower ((DerivedCategory.singleFunctor (SequentialInverseSystem A) (0 : ℤ)).obj M) ≅
      M ⋙ DerivedCategory.singleFunctor A (0 : ℤ) :=
  NatIso.ofComponents
    (fun n ↦ singleTowerComponentIso M (Opposite.unop n))
    (fun f ↦ singleTowerComponentIso_naturality M f)

/-- The canonical tower isomorphism exposes the explicit component isomorphism. -/
@[simp, stacks 0D2L "component of the degree-zero tower isomorphism"]
theorem singleTowerIso_hom_app (M : SequentialInverseSystem A) (n : ℕᵒᵖ) :
    (singleTowerIso M).hom.app n =
      (singleTowerComponentIso M (Opposite.unop n)).hom := sorry

/-- The inverse component of the canonical degree-zero tower isomorphism. -/
@[simp, stacks 0D2L "inverse component of the degree-zero tower isomorphism"]
theorem singleTowerIso_inv_app (M : SequentialInverseSystem A) (n : ℕᵒᵖ) :
    (singleTowerIso M).inv.app n =
      (singleTowerComponentIso M (Opposite.unop n)).inv := sorry

/-- The canonical tower isomorphism in an arbitrary fixed degree. -/
@[stacks 0D2L "fixed-degree stage tower isomorphism"]
noncomputable def singleTowerIsoAt (M : SequentialInverseSystem A) (q : ℤ) :
    tower ((DerivedCategory.singleFunctor (SequentialInverseSystem A) q).obj M) ≅
      M ⋙ DerivedCategory.singleFunctor A q :=
  NatIso.ofComponents
    (fun n ↦ singleTowerComponentIsoAt M q (Opposite.unop n))
    (fun f ↦ singleTowerComponentIsoAt_naturality M q f)

/-- The fixed-degree tower isomorphism exposes its component map. -/
@[simp, stacks 0D2L "component of a fixed-degree tower isomorphism"]
theorem singleTowerIsoAt_hom_app (M : SequentialInverseSystem A) (q : ℤ) (n : ℕᵒᵖ) :
    (singleTowerIsoAt M q).hom.app n =
      (singleTowerComponentIsoAt M q (Opposite.unop n)).hom := sorry

/-- The inverse component of a fixed-degree tower isomorphism. -/
@[simp, stacks 0D2L "inverse component of a fixed-degree tower isomorphism"]
theorem singleTowerIsoAt_inv_app (M : SequentialInverseSystem A) (q : ℤ) (n : ℕᵒᵖ) :
    (singleTowerIsoAt M q).inv.app n =
      (singleTowerComponentIsoAt M q (Opposite.unop n)).inv := sorry

end CategoryTheory.DerivedLimit.Stage
