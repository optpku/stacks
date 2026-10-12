/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap70.Lemma_70_14_4_Pullback
public import stacks_project.Chap71.Lemma_71_5_1_FittingIdeal

/-!
# Lemma 71.5.1

Formation of Fitting ideals of finite-type quasi-coherent modules on algebraic
spaces commutes with inverse image along an arbitrary morphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 71.5.1: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. Let `F` be a finite type, quasi-coherent `𝒪_Y`-module.
Then the inverse-image ideal `(fittingIdealSheaf F i).pullback f` equals the
Fitting ideal `fittingIdealSheaf ((Modules.pullback f).obj F) i`. -/
@[stacks 0CZ4]
theorem fittingIdealSheaf_pullback {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (F : Y.Modules) [F.IsFiniteType] [F.IsQuasicoherent] (i : ℕ) :
    (fittingIdealSheaf F i).pullback f =
      fittingIdealSheaf ((Modules.pullback f).obj F) i :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
