/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Support projections on total complexes

This leaf contains the shape-polymorphic construction which cuts a total-complex summand down to
an arbitrary set of bidegrees.  It is deliberately independent of filtrations, convergence, and
the cochain-specific coordinate choices used by the spectral-sequence API.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape

noncomputable section

universe u v w₁ w₂ w

namespace HomologicalComplex₂

section

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {I₁ : Type w₁} {I₂ : Type w₂} {I : Type w}
variable {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂} {c : ComplexShape I}
variable [TotalComplexShape c₁ c₂ c] [DecidableEq I]
variable (K : HomologicalComplex₂ C c₁ c₂) [K.HasTotal c]

namespace Total.Support

/-- The endomorphism of total degree `n` retaining exactly the bidegrees in `support`. -/
@[stacks 0130 "support cutoff on a total complex"]
noncomputable def cutoff (support : Set (I₁ × I₂)) (n : I) :
    (K.total c).X n ⟶ (K.total c).X n :=
  K.totalDesc fun i j h ↦
    @ite _ ((i, j) ∈ support) (Classical.propDecidable _) (K.ιTotal c i j n h) 0

/-- Restricting a support cutoff to a total-complex summand gives the retained inclusion or zero. -/
@[stacks 0130 "support cutoff on a total-complex summand", reassoc (attr := simp)]
theorem ιTotal_cutoff (support : Set (I₁ × I₂)) (n : I) (i : I₁) (j : I₂)
    (h : ComplexShape.π c₁ c₂ c (i, j) = n) :
    K.ιTotal c i j n h ≫ cutoff K support n =
      @ite _ ((i, j) ∈ support) (Classical.propDecidable _) (K.ιTotal c i j n h) 0 := sorry

/-- A summand in the selected support is fixed by the support cutoff. -/
@[stacks 0130 "support cutoff on a retained summand", reassoc (attr := simp)]
theorem ιTotal_cutoff_of_mem (support : Set (I₁ × I₂)) (n : I) (i : I₁) (j : I₂)
    (h : ComplexShape.π c₁ c₂ c (i, j) = n) (hmem : (i, j) ∈ support) :
    K.ιTotal c i j n h ≫ cutoff K support n = K.ιTotal c i j n h := sorry

/-- A summand outside the selected support is killed by the support cutoff. -/
@[stacks 0130 "support cutoff on a discarded summand", reassoc (attr := simp)]
theorem ιTotal_cutoff_of_not_mem (support : Set (I₁ × I₂)) (n : I) (i : I₁) (j : I₂)
    (h : ComplexShape.π c₁ c₂ c (i, j) = n) (hmem : (i, j) ∉ support) :
    K.ιTotal c i j n h ≫ cutoff K support n = 0 := sorry

section HasImages

variable [HasImages C]

/-- The image subobject cut out by a set of bidegrees in a fixed total degree. -/
@[stacks 0130 "support stage of a total complex"]
noncomputable abbrev stage (support : Set (I₁ × I₂)) (n : I) :
    Subobject ((K.total c).X n) :=
  imageSubobject (cutoff K support n)

end HasImages

section Maps

variable {K L : HomologicalComplex₂ C c₁ c₂}
variable [K.HasTotal c] [L.HasTotal c]

/-- The canonical total map commutes with every bidegree support cutoff. -/
@[stacks 0130 "naturality of a support cutoff"]
theorem cutoff_map (support : Set (I₁ × I₂)) (f : K ⟶ L) (n : I) :
    cutoff K support n ≫ (total.map f c).f n =
      (total.map f c).f n ≫ cutoff L support n := sorry

section StageMaps

variable [HasImages C]

/-- A total map sends the image of one support cutoff into the corresponding target stage. -/
@[stacks 0130 "support stage preservation under total maps"]
theorem stage_factors (support : Set (I₁ × I₂)) (f : K ⟶ L) (n : I) :
    (stage L support n).Factors
      ((stage K support n).arrow ≫ (total.map f c).f n) := sorry

end StageMaps

end Maps

end Total.Support

end

end HomologicalComplex₂
