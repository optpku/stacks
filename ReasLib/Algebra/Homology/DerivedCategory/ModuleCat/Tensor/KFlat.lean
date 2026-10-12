/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.KFlat.ModuleCat.Monoidal
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Tensor
import Mathlib.Tactic.CrossRefAttribute

/-!
# K-flat models for derived tensor products of modules

This leaf records when the canonical two-variable derived-tensor counit is computed by the
ordinary tensor complex.  It is separated from the base tensor instance so users that need only
the derived bifunctor do not acquire the K-flat API.
@stack 064M
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory.DerivedTensor.Bifunctor

variable {R : Type u} [CommRing R]

/-- A K-flat left factor makes the ordinary tensor complex compute the two-variable derived
tensor product. -/
@[stacks 064M "K-flat left factor computes derived tensor"]
theorem counitAppOfComplex_isIso_of_isKFlat_left
    (K L : CochainComplex (ModuleCat.{u} R) ℤ) (hK : K.IsKFlatOver) :
    IsIso (counitAppOfComplex K L) := sorry

/-- A K-flat right factor makes the ordinary tensor complex compute the two-variable derived
tensor product. -/
@[stacks 064M "K-flat right factor computes derived tensor"]
theorem counitAppOfComplex_isIso_of_isKFlat_right
    (K L : CochainComplex (ModuleCat.{u} R) ℤ) (hL : L.IsKFlatOver) :
    IsIso (counitAppOfComplex K L) := sorry

end CategoryTheory.DerivedCategory.DerivedTensor.Bifunctor
