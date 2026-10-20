/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import ReasLib.Algebra.Category.ModuleCat.Flat
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Tensor
public import Mathlib.AlgebraicTopology.DoldKan.Notations
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import ReasLib.AlgebraicTopology.SimplexCategory.FrontBack
import Mathlib.Tactic.CrossRefAttribute

/-!
# Alexander--Whitney comparison for simplicial objects

The comparison is owned here as an actual chain map.  Its degree-`n` component is the finite sum
over `p + q = n` of the front/back face maps into the corresponding total-tensor summand.  The
chain-map law and quasi-isomorphism are propositions and remain separate proof obligations, while
the map itself is concrete data available to downstream constructions.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped DoldKan Simplicial

noncomputable section

universe v u

namespace AlgebraicTopology.AlternatingFaceMapComplex

namespace TensorComparison

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]
  [HasZeroObject C] [(curriedTensor C).Additive]
  [∀ A : C, ((curriedTensor C).obj A).Additive]

/-- The degree-`n` Alexander--Whitney component into the total tensor complex. -/
@[stacks 08QD "Alexander-Whitney degree component"]
def component (X Y : SimplicialObject C) [K[X].HasTensor K[Y]] (n : ℕ) :
    (K[X ⊗ Y]).X n ⟶ (HomologicalComplex.tensorObj K[X] K[Y]).X n :=
  ∑ p : Fin (n + 1),
    let h := Nat.add_sub_of_le (Nat.le_of_lt_succ p.isLt)
    (X.map (SimplexCategory.frontOfAddEq p (n - p) n h).op ⊗ₘ
      Y.map (SimplexCategory.backOfAddEq p (n - p) n h).op) ≫
      HomologicalComplex.ιTensorObj K[X] K[Y] p (n - p) n h

/-- The Alexander--Whitney components commute with the alternating-face differentials. -/
@[stacks 08QD "Alexander-Whitney chain condition"]
theorem component_comm (X Y : SimplicialObject C) [K[X].HasTensor K[Y]] (i j : ℕ)
    (h : (ComplexShape.down ℕ).Rel i j) :
    component X Y i ≫ (HomologicalComplex.tensorObj K[X] K[Y]).d i j =
      (K[X ⊗ Y]).d i j ≫ component X Y j := sorry

end TensorComparison

/-- The concrete Alexander--Whitney chain map `K[X ⊗ Y] ⟶ K[X] ⊗ K[Y]`. -/
@[stacks 08QD "Alexander-Whitney tensor comparison"]
def tensorComparison {C : Type u} [Category.{v} C] [Preadditive C]
    [MonoidalCategory C] [HasZeroObject C] [(curriedTensor C).Additive]
    [∀ A : C, ((curriedTensor C).obj A).Additive]
    (X Y : SimplicialObject C) [K[X].HasTensor K[Y]] :
    K[X ⊗ Y] ⟶ HomologicalComplex.tensorObj K[X] K[Y] where
  f := TensorComparison.component X Y
  comm' := fun i j h ↦ TensorComparison.component_comm X Y i j h

/-- The degreewise formula for the Alexander--Whitney tensor comparison. -/
@[stacks 08QD "Alexander-Whitney tensor comparison component"]
theorem tensorComparison_f {C : Type u} [Category.{v} C] [Preadditive C]
    [MonoidalCategory C] [HasZeroObject C] [(curriedTensor C).Additive]
    [∀ A : C, ((curriedTensor C).obj A).Additive]
    (X Y : SimplicialObject C) [K[X].HasTensor K[Y]] (n : ℕ) :
    (tensorComparison X Y).f n = TensorComparison.component X Y n := sorry

namespace ModuleCat

variable {R : Type u} [CommRing R]

/-- The source-facing flat Eilenberg--Zilber bridge: termwise-flat simplicial modules admit a
quasi-isomorphism from the alternating-face complex of their tensor to the tensor of their
alternating-face complexes.  The canonical Alexander--Whitney map below is a stronger companion;
this existential statement keeps the choice of comparison abstract for downstream arguments. -/
@[stacks 08QD "termwise-flat simplicial-module Eilenberg--Zilber existence"]
theorem exists_quasiIso_of_termwiseFlat
    (X Y : SimplicialObject (_root_.ModuleCat.{u, u} R))
    (hX : ∀ n : ℕ, Module.Flat R (X _⦋n⦌))
    (hY : ∀ n : ℕ, Module.Flat R (Y _⦋n⦌)) :
    ∃ α : (AlgebraicTopology.alternatingFaceMapComplex (_root_.ModuleCat.{u, u} R)).obj
        (X ⊗ Y) ⟶
      HomologicalComplex.tensorObj
        ((AlgebraicTopology.alternatingFaceMapComplex (_root_.ModuleCat.{u, u} R)).obj X)
        ((AlgebraicTopology.alternatingFaceMapComplex (_root_.ModuleCat.{u, u} R)).obj Y),
      QuasiIso α := sorry

/-- The Alexander--Whitney comparison is a quasi-isomorphism for simplicial modules. -/
@[stacks 08QD "Alexander-Whitney quasi-isomorphism", instance]
theorem tensorComparison.quasiIso
    (X Y : SimplicialObject (_root_.ModuleCat.{u, u} R)) :
    QuasiIso (tensorComparison X Y) := sorry

end ModuleCat

end AlgebraicTopology.AlternatingFaceMapComplex
