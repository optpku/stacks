/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.Algebra.Homology.CochainComplexPlus
public import Mathlib.Algebra.Homology.TotalComplex
public import ReasLib.CategoryTheory.Sites.AbelianSheaf

/-!
# Čech complexes of simplicial objects over a site object

Evaluation on the sources of a simplicial object in a slice category gives a cosimplicial
abelian group. Its alternating coface complex extends by zero to integer degrees and gives
the rows of a double complex for complex-valued coefficients.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open ComplexShape

noncomputable section

universe w v u

namespace CategoryTheory.SimplicialObject.Cech

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {U : C}

/-- The nonnegative Čech complex functor evaluates a sheaf on each simplicial source and
uses the alternating sum of coface maps as differential. -/
def complexFunctor (K : SimplicialObject (Over U)) :
    Sheaf J AddCommGrpCat.{w} ⥤ CochainComplex AddCommGrpCat.{w} ℕ :=
  sheafToPresheaf J AddCommGrpCat.{w} ⋙
    (Functor.whiskeringLeft SimplexCategory Cᵒᵖ AddCommGrpCat.{w}).obj
      (K ⋙ Over.forget U).rightOp ⋙
    AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{w}

/-- The degree-`n` Čech term is the section group on the actual degree-`n` simplicial source. -/
theorem complexFunctor_obj_X (K : SimplicialObject (Over U))
    (F : Sheaf J AddCommGrpCat.{w}) (n : ℕ) :
    ((complexFunctor K).obj F).X n =
      F.obj.obj (op ((K.obj (op (SimplexCategory.mk n))).left)) := by
  rfl

/-- The integer-indexed Čech row is the extension by zero of the nonnegative Čech complex. -/
abbrev rowFunctor (K : SimplicialObject (Over U)) :
    Sheaf J AddCommGrpCat.{w} ⥤ CochainComplex AddCommGrpCat.{w} ℤ :=
  complexFunctor K ⋙ embeddingUpNat.extendFunctor AddCommGrpCat.{w}

/-- Evaluating the Čech row extends the nonnegative Čech complex by zero. -/
theorem rowFunctor_obj (K : SimplicialObject (Over U))
    (F : Sheaf J AddCommGrpCat.{w}) :
    (rowFunctor K).obj F = ((complexFunctor K).obj F).extend embeddingUpNat := by
  rfl

/-- The Čech row functor preserves zero morphisms. -/
instance rowFunctor_preservesZeroMorphisms (K : SimplicialObject (Over U)) :
    (rowFunctor (J := J) K).PreservesZeroMorphisms := by
  constructor
  intro F G
  apply HomologicalComplex.hom_ext
  intro n
  change HomologicalComplex.extend.mapX ((complexFunctor K).map (0 : F ⟶ G))
    (embeddingUpNat.r n) = 0
  cases embeddingUpNat.r n with
  | none => rfl
  | some m => rfl

/-- Applying the Čech row degreewise gives the Čech double complex of a coefficient complex. -/
abbrev doubleFunctor (K : SimplicialObject (Over U)) :
    CochainComplex (Sheaf J AddCommGrpCat.{w}) ℤ ⥤
      HomologicalComplex₂ AddCommGrpCat.{w} (up ℤ) (up ℤ) :=
  (rowFunctor K).mapHomologicalComplex (up ℤ)

/-- The Čech double complex is obtained by applying the row functor degreewise. -/
theorem doubleFunctor_obj (K : SimplicialObject (Over U))
    (ℰ : CochainComplex (Sheaf J AddCommGrpCat.{w}) ℤ) :
    (doubleFunctor K).obj ℰ = ((rowFunctor K).mapHomologicalComplex (up ℤ)).obj ℰ := by
  rfl

/-- The total Čech complex functor totalizes the integer-indexed Čech double complex. -/
abbrev totalFunctor (K : SimplicialObject (Over U)) :
    CochainComplex (Sheaf J AddCommGrpCat.{w}) ℤ ⥤ CochainComplex AddCommGrpCat.{w} ℤ :=
  doubleFunctor K ⋙
    HomologicalComplex₂.totalFunctor AddCommGrpCat.{w} (up ℤ) (up ℤ) (up ℤ)

/-- Evaluating the total Čech functor recovers the total complex of the Čech double complex. -/
theorem totalFunctor_obj (K : SimplicialObject (Over U))
    (ℰ : CochainComplex (Sheaf J AddCommGrpCat.{w}) ℤ) :
    (totalFunctor K).obj ℰ =
      HomologicalComplex₂.total ((doubleFunctor K).obj ℰ) (up ℤ) := by
  rfl

/-- The total Čech complex of a bounded-below coefficient complex is bounded below. -/
theorem totalPlus_obj_mem (K : SimplicialObject (Over U))
    (ℰ : CochainComplex.Plus (Sheaf J AddCommGrpCat.{w})) :
    CochainComplex.plus AddCommGrpCat.{w}
      ((CochainComplex.Plus.ι (Sheaf J AddCommGrpCat.{w}) ⋙ totalFunctor K).obj ℰ) := by
  obtain ⟨a, ha⟩ := ℰ.property
  refine ⟨a, ?_⟩
  rw [CochainComplex.isStrictlyGE_iff]
  intro n hn
  rw [IsZero.iff_id_eq_zero]
  apply HomologicalComplex₂.total.hom_ext
  intro p q hpq
  have hz : IsZero ((((doubleFunctor K).obj ℰ.obj).X p).X q) := by
    by_cases hp : p < a
    · exact (HomologicalComplex.eval _ _ q).map_isZero
        ((rowFunctor K).map_isZero
          ((CochainComplex.isStrictlyGE_iff ℰ.obj a).mp ha p hp))
    · change IsZero ((((complexFunctor K).obj (ℰ.obj.X p)).extend embeddingUpNat).X q)
      exact CochainComplex.isZero_of_isStrictlyGE _ 0 q (by
        change p + q = n at hpq
        omega)
  exact hz.eq_of_src _ _

/-- The total Čech functor restricted to bounded-below coefficient complexes. -/
def totalPlus (K : SimplicialObject (Over U)) :
    CochainComplex.Plus (Sheaf J AddCommGrpCat.{w}) ⥤ CochainComplex.Plus AddCommGrpCat.{w} :=
  (CochainComplex.plus AddCommGrpCat.{w}).lift
    (CochainComplex.Plus.ι (Sheaf J AddCommGrpCat.{w}) ⋙ totalFunctor K)
    (totalPlus_obj_mem K)

/-- Forgetting boundedness after the bounded-below total Čech functor recovers totalization. -/
theorem totalPlus_comp_ι (K : SimplicialObject (Over U)) :
    totalPlus (J := J) K ⋙ CochainComplex.Plus.ι AddCommGrpCat.{w} =
      CochainComplex.Plus.ι (Sheaf J AddCommGrpCat.{w}) ⋙ totalFunctor K := by
  rfl

end CategoryTheory.SimplicialObject.Cech
