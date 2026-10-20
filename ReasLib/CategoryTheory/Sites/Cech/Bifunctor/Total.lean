/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Cech.Bifunctor
public import ReasLib.CategoryTheory.GradedObject.Monoidal.MapObj
import Mathlib.Tactic.CrossRefAttribute

/-!
@stack 07MB

# Heterogeneous tensor comparisons of total Cech complexes

This file assembles the natural-degree front/back Cech map across the two external complex
degrees.  The coefficient operation remains an explicit curried bifunctor
`T : A ⥤ B ⥤ D`; consequently the construction applies to tensor products of modules in
different universes and does not require a monoidal unit in any coefficient category.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open ComplexShape HomologicalComplex HomologicalComplex₂

noncomputable section

universe w uA vA uB vB uD vD v u

namespace CategoryTheory.Cech.Bifunctor.Total

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C]
variable {A : Type uA} [Category.{vA} A] [Preadditive A]
variable [HasZeroObject A] [HasProducts.{w} A] [HasCoproducts A]
variable {B : Type uB} [Category.{vB} B] [Preadditive B]
variable [HasZeroObject B] [HasProducts.{w} B] [HasCoproducts B]
variable {D : Type uD} [Category.{vD} D] [Preadditive D]
variable [HasZeroObject D] [HasProducts.{w} D] [HasCoproducts D]
variable {ι : Type w}
variable (T : A ⥤ B ⥤ D)
variable [T.PreservesZeroMorphisms] [∀ X, (T.obj X).PreservesZeroMorphisms]
variable [∀ X : A, PreservesColimitsOfSize.{0, 0} (T.obj X)]
variable [∀ Y : B, PreservesColimitsOfSize.{0, 0} (T.flip.obj Y)]
variable (U : ι → C)
variable (F : CochainComplex (Cᵒᵖ ⥤ A) ℤ)
variable (G : CochainComplex (Cᵒᵖ ⥤ B) ℤ)

/-- The heterogeneous total of the two total Cech complexes. -/
@[stacks 07MB "source of the heterogeneous total Cech comparison"]
abbrev source : CochainComplex D ℤ :=
  HomologicalComplex.mapBifunctor
    ((Cech.Total.totalCechFunctor (A := A) U).obj F)
    ((Cech.Total.totalCechFunctor (A := B) U).obj G) T (up ℤ)

/-- The total Cech complex of the pointwise heterogeneous total of the coefficient complexes. -/
@[stacks 07MB "target of the heterogeneous total Cech comparison"]
abbrev target : CochainComplex D ℤ :=
  (Cech.Total.totalCechFunctor (A := D) U).obj
    (HomologicalComplex.mapBifunctor F G (pointwiseFunctor T) (up ℤ))

/-- Descend homogeneous components into one degree of the heterogeneous source total. -/
@[stacks 07MB "homogeneous descent for the heterogeneous total Cech comparison"]
abbrev componentMap (n : ℤ) {M : D}
    (f : ∀ p q (_ : p + q = n),
      (T.obj (((Cech.Total.totalCechFunctor (A := A) U).obj F).X p)).obj
        (((Cech.Total.totalCechFunctor (A := B) U).obj G).X q) ⟶ M) :
    (source T U F G).X n ⟶ M :=
  HomologicalComplex.mapBifunctorDesc
    (K₁ := (Cech.Total.totalCechFunctor (A := A) U).obj F)
    (K₂ := (Cech.Total.totalCechFunctor (A := B) U).obj G)
    (F := T) (c := up ℤ) f

/-- Reassociate the external and Cech degrees after fixing the source total degree. -/
@[stacks 07MB "degree rearrangement for a heterogeneous total Cech comparison"]
theorem totalDegree {p q n : ℤ} (hpq : p + q = n) {x y : ℤ × ℤ}
    (hx : ComplexShape.π (up ℤ) (up ℤ) (up ℤ) x = p)
    (hy : ComplexShape.π (up ℤ) (up ℤ) (up ℤ) y = q) :
    ComplexShape.π (up ℤ) (up ℤ) (up ℤ)
      (x.1 + y.1, x.2 + y.2) = n := sorry

/-- The explicit four-degree component of the heterogeneous total Cech comparison. -/
@[stacks 07MB "four-degree component of the heterogeneous total Cech comparison"]
noncomputable def component (n : ℤ) {a b : ℤ} (h : a + b = n) :
    (T.obj (((Cech.Total.totalCechFunctor (A := A) U).obj F).X a)).obj
        (((Cech.Total.totalCechFunctor (A := B) U).obj G).X b) ⟶
      (target T U F G).X n :=
  GradedObject.mapObjBifunctorDesc
    (((Cech.Total.doubleCechFunctor (A := A) U).obj F).toGradedObject)
    (((Cech.Total.doubleCechFunctor (A := B) U).obj G).toGradedObject)
    (ComplexShape.π (up ℤ) (up ℤ) (up ℤ))
    (ComplexShape.π (up ℤ) (up ℤ) (up ℤ)) (T := T) a b
    (fun x hx y hy ↦
      (ComplexShape.σ (up ℤ) (up ℤ) (up ℤ) x.2 y.1) •
        (HomologicalComplex.ιMapBifunctor
            ((Cech.Total.rowCechFunctor (A := A) U).obj (F.X x.1))
            ((Cech.Total.rowCechFunctor (A := B) U).obj (G.X y.1))
            T (up ℤ) x.2 y.2 (x.2 + y.2) rfl ≫
          (rowComparisonZ T U (F.X x.1) (G.X y.1)).f (x.2 + y.2) ≫
          ((Cech.Total.rowCechFunctor (A := D) U).map
            (HomologicalComplex.ιMapBifunctor F G (pointwiseFunctor T) (up ℤ)
              x.1 y.1 (x.1 + y.1) rfl)).f (x.2 + y.2) ≫
          (((Cech.Total.doubleCechFunctor (A := D) U).obj
            (HomologicalComplex.mapBifunctor F G (pointwiseFunctor T) (up ℤ))).ιTotal
              (up ℤ) (x.1 + y.1) (x.2 + y.2) n (totalDegree h hx hy))))

/-- The heterogeneous four-degree components commute with the total differentials. -/
@[stacks 07MB "chain compatibility of heterogeneous total Cech components"]
theorem component_comm (i j : ℤ) (hij : (up ℤ).Rel i j) :
    componentMap T U F G i (fun _ _ h ↦ component T U F G i h) ≫
        (target T U F G).d i j =
      (source T U F G).d i j ≫
        componentMap T U F G j (fun _ _ h ↦ component T U F G j h) := sorry

/-- 20.25.3.2 (07MB): the canonical heterogeneous comparison from the tensor total of two Cech
totals to the Cech total of their pointwise tensor total. -/
@[stacks 07MB "canonical heterogeneous total Cech comparison"]
noncomputable def comparison : source T U F G ⟶ target T U F G :=
  HomologicalComplex.Hom.mk
    (fun n ↦ componentMap T U F G n (fun _ _ h ↦ component T U F G n h))
    (component_comm T U F G)

/-- The degree component of the canonical heterogeneous total Cech comparison. -/
@[simp, stacks 07MB "degree component of the heterogeneous total Cech comparison"]
theorem comparison_f (n : ℤ) :
    (comparison T U F G).f n =
      componentMap T U F G n (fun _ _ h ↦ component T U F G n h) := sorry

/-- The heterogeneous total Cech comparison is natural in both coefficient complexes. -/
@[stacks 07MB "naturality of the heterogeneous total Cech comparison"]
theorem comparison_naturality
    {F' : CochainComplex (Cᵒᵖ ⥤ A) ℤ} {G' : CochainComplex (Cᵒᵖ ⥤ B) ℤ}
    (f : F ⟶ F') (g : G ⟶ G') :
    HomologicalComplex.mapBifunctorMap
        ((Cech.Total.totalCechFunctor (A := A) U).map f)
        ((Cech.Total.totalCechFunctor (A := B) U).map g) T (up ℤ) ≫
      comparison T U F' G' =
    comparison T U F G ≫
      (Cech.Total.totalCechFunctor (A := D) U).map
        (HomologicalComplex.mapBifunctorMap f g (pointwiseFunctor T) (up ℤ)) := sorry

end CategoryTheory.Cech.Bifunctor.Total

end
