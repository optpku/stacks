/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Manifold.Sheaf.Smooth
import StacksCheckRecall

@[expose] public section

open Manifold Opposite TopologicalSpace
open scoped ContDiff

noncomputable section

variable (n : ℕ)

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "𝒪∞" => smoothSheaf (𝓘(ℝ, E)) 𝓘(ℝ) E ℝ

/-
The canonical owner `smoothSheaf` already packages smooth real-valued functions as a sheaf of
types, while `smoothSheaf.obj_eq` identifies its sections with `C^∞` maps and the inherited
`Module ℝ` instance supplies the source's vector-space structure. The generic concrete-presheaf
stalk API then gives representatives and equality of germs, so no smooth-specific wrapper is
needed and later stalk arguments can reuse the canonical theorems directly.
-/

/- Example 6.11.4 (1): the presheaf of smooth real-valued functions on `ℝ^n` is the canonical
sheaf `smoothSheaf (𝓘(ℝ, E)) 𝓘(ℝ) E ℝ`; its value on an open set is definitionally the type of
smooth functions on that open set. -/
@[stacks 007C "smooth real-valued functions form a sheaf"]
recall smoothSheaf

/- The section type of the canonical smooth sheaf is definitionally the corresponding `C^∞` map type. -/
recall smoothSheaf.obj_eq

/- Example 6.11.4 (2): sections of the smooth real-valued sheaf on every open set of `ℝ^n` carry
their canonical `ℝ`-vector-space structure. -/
@[stacks 007C "smooth sections form real vector spaces"]
#check fun U : (Opens E)ᵒᵖ ↦
  (inferInstance : Module ℝ C^∞⟮𝓘(ℝ, E), (unop U : Opens E); 𝓘(ℝ), ℝ⟯)

/- Example 6.11.4 (3): every element of the stalk of the smooth sheaf at `x` is represented by a
smooth function defined on an open neighbourhood of `x`. -/
@[stacks 007C "stalk elements have smooth local representatives"]
recall TopCat.Presheaf.exists_germ_eq

/- Example 6.11.4 (4): if two smooth functions defined near `x` determine the same stalk element,
their restrictions agree on a smaller open neighbourhood of `x`. -/
@[stacks 007C "equal germs imply local agreement"]
recall TopCat.Presheaf.germ_eq

/- Example 6.11.4 (5): agreement on a smaller open neighbourhood implies that two smooth functions
defined near `x` determine the same stalk element. -/
@[stacks 007C "local agreement implies equal germs"]
recall TopCat.Presheaf.germ_ext
