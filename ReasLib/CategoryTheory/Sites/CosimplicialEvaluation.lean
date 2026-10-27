/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.Evaluation
public import Mathlib.CategoryTheory.Sites.Abelian

/-!
# Evaluation on indexed cosimplicial families

A covariant family of cosimplicial objects and a coefficient presheaf give a simplicial
presheaf on the indexing category. Its alternating-face complex can be sheafified degreewise.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicTopology
open scoped Simplicial

noncomputable section

universe u v u' v' w w'

namespace CategoryTheory.CosimplicialObject.Evaluation.Family

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
variable {A : Type w} [Category.{w'} A] [Abelian A]
variable (T : C ⥤ CosimplicialObject D) (F : Dᵒᵖ ⥤ A)

/-- Evaluating a coefficient presheaf on an indexed cosimplicial family gives a simplicial
presheaf on its indexing category. -/
def simplicial : SimplicialObject (Cᵒᵖ ⥤ A) :=
  (T.op ⋙ (cosimplicialSimplicialEquiv D).functor ⋙
    (Functor.whiskeringRight SimplexCategoryᵒᵖ Dᵒᵖ A).obj F).flip

/-- The alternating-face complex of the simplicial presheaf obtained by family evaluation. -/
def presheafComplex : ChainComplex (Cᵒᵖ ⥤ A) ℕ :=
  (alternatingFaceMapComplex (Cᵒᵖ ⥤ A)).obj (simplicial T F)

/-- A family morphism induces a contravariant map of evaluated alternating-face complexes. -/
def chainMap {U V : C} (g : V ⟶ U) :
    (Evaluation.complex A (T.obj U)).obj F ⟶
      (Evaluation.complex A (T.obj V)).obj F :=
  (alternatingFaceMapComplex A).map ((simplicial T F).flip.map g.op)

/-- The degree component of the chain map is evaluation on the corresponding family map. -/
theorem chainMap_f {U V : C} (g : V ⟶ U) (n : ℕ) :
    (chainMap T F g).f n = F.map (op ((T.map g).app ⦋n⦌)) :=
  sorry

/-- The presheaf in a fixed degree of cosimplicial family evaluation. -/
def presheafDegree (n : ℕ) : Cᵒᵖ ⥤ A :=
  (presheafComplex T F).X n

/-- The degreewise values of the presheaf complex are the individual evaluation complexes. -/
theorem presheafComplex_X (n : ℕ) (U : Cᵒᵖ) :
    ((presheafComplex T F).X n).obj U =
      ((Evaluation.complex A (T.obj U.unop)).obj F).X n :=
  sorry

variable (J : GrothendieckTopology C) [HasSheafify J A]

/-- Degreewise sheafification of the alternating-face presheaf complex. -/
def sheafChain : ChainComplex (Sheaf J A) ℕ :=
  ((presheafToSheaf J A).mapHomologicalComplex (ComplexShape.down ℕ)).obj
    (presheafComplex T F)

/-- The sheafified evaluation complex, with chain degree `n` placed in cochain degree `-n`. -/
def sheafComplex : CochainComplex (Sheaf J A) ℤ :=
  (ComplexShape.embeddingDownNat.extendFunctor (Sheaf J A)).obj (sheafChain T F J)

/-- Each chain degree is the associated sheaf of the corresponding evaluation presheaf. -/
theorem sheafChain_X (n : ℕ) :
    (sheafChain T F J).X n =
      (presheafToSheaf J A).obj ((presheafComplex T F).X n) :=
  sorry

/-- In cochain degree `-n`, the sheafified complex is the associated degree-`n` presheaf. -/
theorem sheafComplex_X_neg (n : ℕ) :
    (sheafComplex T F J).X (-(n : ℤ)) =
      (presheafToSheaf J A).obj ((presheafComplex T F).X n) :=
  sorry

end CategoryTheory.CosimplicialObject.Evaluation.Family
