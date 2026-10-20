/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.Opposite
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Opposite model of the alternating coface complex

This module isolates the variance bridge used by the cosimplicial Dold--Kan correspondence.
It identifies the alternating coface complex with the unopposite of the alternating face complex
of the corresponding simplicial object in the opposite category.
-/

@[expose] public section

open CategoryTheory
open AlgebraicTopology

noncomputable section

universe u v

namespace CategoryTheory.CosimplicialObject.DoldKan

variable {A : Type u} [Category.{v} A] [Preadditive A]

namespace alternatingCoface
namespace opposite

/-- The alternating face complex of the opposite simplicial object, transported back to `A`. -/
@[stacks 019I "opposite-simplicial model of the alternating coface complex"]
abbrev complex :
    CosimplicialObject A ⥤ CochainComplex A ℕ :=
  ((CategoryTheory.cosimplicialSimplicialEquiv A).functor ⋙
      (AlgebraicTopology.alternatingFaceMapComplex Aᵒᵖ)).rightOp ⋙
    HomologicalComplex.unopFunctor A (ComplexShape.down ℕ)

/-- The identity degreewise maps intertwine the source-facing and opposite-simplicial
differentials. -/
@[stacks 019I "differential compatibility of the opposite-model comparison"]
theorem appIso.comm
    (U : CosimplicialObject A) (i j : ℕ) (hij : (ComplexShape.up ℕ).Rel i j) :
    (Iso.refl (((alternatingCofaceMapComplex A).obj U).X i)).hom ≫
        (complex.obj U).d i j =
      ((alternatingCofaceMapComplex A).obj U).d i j ≫
        (Iso.refl (((alternatingCofaceMapComplex A).obj U).X j)).hom := sorry

/-- The canonical objectwise comparison between the alternating coface complex and its
opposite-simplicial model. -/
@[stacks 019I "objectwise opposite-model comparison"]
def appIso (U : CosimplicialObject A) :
    (alternatingCofaceMapComplex A).obj U ≅ complex.obj U :=
  HomologicalComplex.Hom.isoOfComponents (fun _ ↦ Iso.refl _)
    (appIso.comm U)

/-- The forward opposite-model comparison is the identity in every degree. -/
@[simp, stacks 019I "forward component of the opposite-model comparison"]
theorem appIso.hom.f (U : CosimplicialObject A) (n : ℕ) :
    (appIso U).hom.f n = 𝟙 _ := sorry

/-- The inverse opposite-model comparison is the identity in every degree. -/
@[simp, stacks 019I "inverse component of the opposite-model comparison"]
theorem appIso.inv.f (U : CosimplicialObject A) (n : ℕ) :
    (appIso U).inv.f n = 𝟙 _ := sorry

/-- The objectwise comparisons with the opposite-simplicial model are natural. -/
@[reassoc, stacks 019I "naturality of the opposite-model comparison"]
theorem appIso.naturality
    {U V : CosimplicialObject A} (f : U ⟶ V) :
    (alternatingCofaceMapComplex A).map f ≫
        (appIso V).hom =
      (appIso U).hom ≫ complex.map f := sorry

/-- The alternating coface complex is naturally isomorphic to the transported alternating face
complex of the opposite simplicial object. -/
@[stacks 019I "opposite model of the alternating coface complex"]
def iso :
    alternatingCofaceMapComplex A ≅ complex :=
  NatIso.ofComponents appIso (fun f ↦ appIso.naturality f)

/-- The component of the opposite-model natural isomorphism is the objectwise comparison. -/
@[simp, stacks 019I "component of the opposite-model natural isomorphism"]
theorem iso.app (U : CosimplicialObject A) :
    (iso (A := A)).app U = appIso U := sorry

end opposite
end alternatingCoface

end CategoryTheory.CosimplicialObject.DoldKan
