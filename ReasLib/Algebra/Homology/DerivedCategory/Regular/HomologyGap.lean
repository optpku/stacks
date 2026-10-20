/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
public import ReasLib.Algebra.Homology.DerivedCategory.Perfect
public import ReasLib.CategoryTheory.DerivedCategory.Bounded.Homology
public import ReasLib.RingTheory.GlobalDimension.Regular
import Mathlib.Tactic.CrossRefAttribute

/-!
# Cohomology gaps over regular rings

@stack 0FXJ
@stack 0FXK

Finite global dimension turns a sufficiently wide cohomology gap into morphism vanishing.  For a
perfect complex, that vanishing splits the corresponding truncation triangle.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open DerivedCategory DerivedCategory.TStructure

universe u

-- Local instance justification (search instability): the gap statements use the standard
-- t-structure on the derived category of modules.
attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

variable {R : Type u} [CommRing R] [IsRegularRing R]

local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat R)

/-- Lemma 15.80.3 (0FXJ): over a finite-dimensional regular ring, a cohomology gap between two
bounded-above derived objects forces every morphism between them to vanish. -/
@[stacks 0FXJ "hom vanishing across a regular-dimension gap"]
theorem hom_eq_zero_of_boundedAbove_of_homology_gap_over_regularRing
    (d : ℕ) (hdim : ringKrullDim R = d) (K : D⁻((ModuleCat R)))
    {L : DMod} {k : ℤ} (hK : K.obj.IsGE (k + 1)) (hL : L.IsLE (k - d))
    (f : K.obj ⟶ L) :
    f = 0 := sorry

/-- Lemma 15.80.4 (0FXK): a cohomology gap in a perfect complex over a positive-dimensional
regular ring splits its canonical truncation triangle. -/
@[stacks 0FXK "splitting across a cohomology gap"]
theorem exists_truncation_gap_biprod_of_isPerfect_of_homology_vanishing
    (d : ℕ) (hd : 1 ≤ d) (hdim : ringKrullDim R = d) (K : DMod) (k : ℤ)
    (hperfect : K.IsPerfect)
    (hvanish : ∀ i : ℤ, k - d + 2 ≤ i → i ≤ k → IsZero ((H i).obj K)) :
    ∃ e : K ≅ (t.truncLE (k - d + 1)).obj K ⊞ (t.truncGE (k + 1)).obj K,
      ((t.truncLEι (k - d + 1)).app K) ≫ e.hom = biprod.inl ∧
        e.hom ≫ biprod.snd = (t.truncGEπ (k + 1)).app K := sorry

end CategoryTheory
