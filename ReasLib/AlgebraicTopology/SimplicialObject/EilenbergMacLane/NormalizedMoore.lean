/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicTopology.DoldKan.Equivalence
public import ReasLib.AlgebraicTopology.SimplicialObject.EilenbergMacLane.Functor

/-!
@stack 0199

# Normalized Moore complex of an Eilenberg-MacLane object

Applying the normalized Moore functor to `K(B, k)` recovers the chain complex concentrated in
degree `k`.  This file uses Mathlib's initial-face (`d₀`) normalization.  The source final-face
convention is owned by `DoldKan.N.lowerFace` and its source-oriented extension leaves.  This file
owns the functorial comparison and its degreewise object consequences; alternating-face homology
lives in the separate `Homology` module.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Abelian.DoldKan HomologicalComplex
open scoped Simplicial

noncomputable section

universe v u

namespace CategoryTheory.SimplicialObject.eilenbergMacLane.normalizedMoore

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- The normalized Moore complex of the Eilenberg-MacLane functor is naturally isomorphic to the
single-complex functor in its defining degree. -/
@[stacks 0199 "d₀-oriented functorial Eilenberg-MacLane normalized Moore comparison"]
noncomputable def iso (k : ℕ) :
    eilenbergMacLane.functor k ⋙ AlgebraicTopology.normalizedMooreComplex A ≅
      single A (ComplexShape.down ℕ) k :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (single A (ComplexShape.down ℕ) k) equivalence.counitIso ≪≫
      Functor.rightUnitor _

/-- The component of the normalized Moore comparison is the Dold-Kan counit component. -/
@[simp, stacks 0199 "d₀-oriented Eilenberg-MacLane normalized Moore comparison component formula"]
theorem iso_app (k : ℕ) (X : A) :
    (iso (A := A) k).app X =
      equivalence.counitIso.app ((single A (ComplexShape.down ℕ) k).obj X) := sorry

/-- Degree `k` of the normalized Moore complex of `K(B, k)` is canonically isomorphic to `B`. -/
@[stacks 0199 "normalized Moore complex of an Eilenberg-MacLane object"]
noncomputable def objIso (B : A) (k : ℕ) :
    ((AlgebraicTopology.normalizedMooreComplex A).obj (eilenbergMacLane B k)).X k ≅ B :=
  (HomologicalComplex.eval A (ComplexShape.down ℕ) k).mapIso
      ((iso (A := A) k).app B) ≪≫
    singleObjXSelf (ComplexShape.down ℕ) k B

/-- The degree-`k` normalized Moore comparisons are natural in the coefficient object. -/
@[stacks 0199 "normalized Moore degree comparison naturality"]
theorem objIso.hom_naturality (k : ℕ) {B D : A} (f : B ⟶ D) :
    ((eilenbergMacLane.functor k ⋙
        AlgebraicTopology.normalizedMooreComplex A).map f).f k ≫
          (objIso D k).hom =
      (objIso B k).hom ≫ f := sorry

/-- The inverse degree-`k` normalized Moore comparisons are natural in the coefficient
object. -/
@[stacks 0199 "inverse normalized Moore degree comparison naturality"]
theorem objIso.inv_naturality (k : ℕ) {B D : A} (f : B ⟶ D) :
    f ≫ (objIso D k).inv =
      (objIso B k).inv ≫
        ((eilenbergMacLane.functor k ⋙
          AlgebraicTopology.normalizedMooreComplex A).map f).f k := sorry

/-- Degree `k` of the normalized Moore complex of the Eilenberg-MacLane functor is naturally
isomorphic to the identity functor. -/
@[stacks 0199 "functorial degreewise normalized Moore comparison"]
noncomputable def evalIso (k : ℕ) :
    (eilenbergMacLane.functor k ⋙ AlgebraicTopology.normalizedMooreComplex A) ⋙
        HomologicalComplex.eval A (ComplexShape.down ℕ) k ≅ 𝟭 A :=
  NatIso.ofComponents (fun B ↦ objIso B k) (fun f ↦ objIso.hom_naturality k f)

/-- The component of the degreewise normalized Moore comparison is `objIso`. -/
@[simp, stacks 0199 "degreewise normalized Moore comparison component formula"]
theorem evalIso_app (k : ℕ) (B : A) :
    (evalIso (A := A) k).app B = objIso B k := sorry

/-- Away from degree `k`, evaluation of the normalized Moore complex of the
Eilenberg-MacLane functor is the zero functor. -/
@[stacks 0199 "functorial off-degree normalized Moore vanishing"]
theorem isZero_comp_eval (k i : ℕ) (h : i ≠ k) :
    IsZero
      ((eilenbergMacLane.functor k ⋙ AlgebraicTopology.normalizedMooreComplex A) ⋙
        HomologicalComplex.eval A (ComplexShape.down ℕ) i) := sorry

/-- Away from degree `k`, the normalized Moore complex of `K(B, k)` vanishes. -/
@[stacks 0199 "off-degree normalized Moore vanishing"]
theorem isZero (B : A) (k i : ℕ) (h : i ≠ k) :
    IsZero (((AlgebraicTopology.normalizedMooreComplex A).obj
      (eilenbergMacLane B k)).X i) := sorry

end CategoryTheory.SimplicialObject.eilenbergMacLane.normalizedMoore
