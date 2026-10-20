/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.AlgebraicTopology.CechNerve
public import ReasLib.Algebra.Category.CommAlgCat.Module
public import ReasLib.AlgebraicTopology.CosimplicialObject.Augmented.AlternatingCoface

/-!
# The augmented Amitsur complex

This module constructs the augmented Amitsur complex of a commutative algebra with
coefficients in a module.  The algebraic Čech conerve supplies all tensor powers and their
cofaces; forgetting to modules and tensoring on the right supplies the coefficients.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicTopology ModuleCat
open CategoryTheory.MonoidalCategory
open scoped MonoidalCategory TensorProduct

universe u

namespace Algebra.Amitsur

variable (R A M : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module R M]

/-- The arrow from the base algebra to the given algebra whose Čech conerve underlies the
Amitsur construction. -/
abbrev ringArrow : Arrow (CommAlgCat R) :=
  Arrow.mk (CommAlgCat.ofHom (Algebra.ofId R A))

/-- The functor which forgets an `R`-algebra to an `R`-module and then tensors it on the right
with the coefficient module `M`. -/
abbrev coefficientFunctor : CommAlgCat R ⥤ ModuleCat R :=
  CommAlgCat.forgetToModule R ⋙ tensorRight (ModuleCat.of R M)

/-- The augmented algebraic Čech conerve after forgetting to modules and tensoring with `M`.
Its augmentation point is canonically isomorphic to `M`. -/
abbrev tensorAugmented : CosimplicialObject.Augmented (ModuleCat R) :=
  ((CosimplicialObject.Augmented.whiskering (CommAlgCat R) (ModuleCat R)).obj
    (coefficientFunctor R M)).obj (ringArrow R A).augmentedCechConerve

/-- The augmented cosimplicial `R`-module defining the Amitsur complex, with augmentation
point exactly `M`. -/
def augmented : CosimplicialObject.Augmented (ModuleCat R) where
  left := ModuleCat.of R M
  right := (tensorAugmented R A M).right
  hom := (CosimplicialObject.const (ModuleCat R)).map ((λ_ (ModuleCat.of R M)).symm.hom) ≫
    (tensorAugmented R A M).hom

/-- The ordinary nonnegative Amitsur cochain complex, before adjoining the coefficient module
in degree zero. -/
abbrev complex : CochainComplex (ModuleCat R) ℕ :=
  (alternatingCofaceMapComplex (ModuleCat R)).obj (augmented R A M).right

/-- The canonical map from `M` to the degree-zero object of the ordinary Amitsur complex. -/
abbrev augmentationMap : ModuleCat.of R M ⟶ (complex R A M).X 0 :=
  (augmented R A M).hom.app (SimplexCategory.mk 0)

/-- The canonical augmentation from `M` concentrated in degree zero to the ordinary Amitsur
complex. -/
abbrev augmentation :
    (CochainComplex.single₀ (ModuleCat R)).obj (ModuleCat.of R M) ⟶ complex R A M :=
  AlternatingCofaceMapComplex.coaugmentationApp (augmented R A M)

/-- The augmented Amitsur cochain complex.  Lean degree `0` is textbook degree `-1`, occupied
by `M`; Lean degree `n + 1` is the alternating Čech term of textbook degree `n`. -/
def extended : CochainComplex (ModuleCat R) ℕ :=
  AlternatingCofaceMapComplex.extended (augmented R A M)

/-- The coefficient module is the degree-zero object of the augmented Amitsur complex. -/
theorem extended_X_zero : (extended R A M).X 0 = ModuleCat.of R M := sorry

/-- Positive degrees of the augmented Amitsur complex are the degrees of its ordinary
alternating-coface complex. -/
theorem extended_X_succ (n : ℕ) :
    (extended R A M).X (n + 1) = (complex R A M).X n := sorry

/-- The first differential of the augmented Amitsur complex is its canonical augmentation
map, corresponding to `m ↦ 1 ⊗ₜ[R] m`. -/
theorem extended_d_zero_one :
    (extended R A M).d 0 1 = augmentationMap R A M := sorry

end Algebra.Amitsur

end
