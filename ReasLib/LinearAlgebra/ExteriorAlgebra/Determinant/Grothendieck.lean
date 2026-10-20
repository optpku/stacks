/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.LinearAlgebra.ExteriorAlgebra.Determinant.ShortExact
public import ReasLib.LinearAlgebra.ExteriorAlgebra.Determinant.Invertible
public import ReasLib.Algebra.Category.ModuleCat.GrothendieckGroup.Basic
public import ReasLib.RingTheory.PicardGroup.Invertible
import Mathlib.Tactic.CrossRefAttribute

/-!
# Determinant on the projective Grothendieck group

The determinant line of a finite-projective module is multiplicative across a short exact row.
This leaf records the corresponding invariant on the property-indexed projective Grothendieck
group.  Since `K₀` is additive while `CommRing.Pic R` is multiplicative, the target is represented
by the canonical additive wrapper `Additive (CommRing.Pic R)`.

@stack 0AFX
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped Module.Determinant

universe u v

namespace CategoryTheory.ModuleCat.K0.Projective

variable (R : Type u) [CommRing R]

/-- The determinant Picard class of a finite-projective module, in additive target form. -/
@[stacks 0AFX "determinant Picard class of a finite-projective module"]
abbrev detClass (M : ModuleCat.FiniteProjective.{u, v} R) :
    Additive (CommRing.Pic R) :=
  Additive.ofMul (CommRing.Pic.mk R (det[R](M.obj)))

/-- The determinant class kills every defining short-exact relation in projective `K₀`. -/
@[stacks 0AFX "determinant class kills projective K0 relations"]
theorem relations_le_ker_det :
    ObjectProperty.GrothendieckGroup.relations (ModuleCat.finiteProjective.{u, v} R) ≤
      (FreeAbelianGroup.lift (detClass R)).ker := sorry
-- Proof strategy: check each generating short-exact relation; use `determinantTensorIso` to
-- identify the middle determinant line with the tensor product of the outer determinant lines,
-- then translate this isomorphism through `CommRing.Pic.mk` and the additive wrapper.

/-- The determinant homomorphism from projective `K₀(R)` to the Picard group of `R`. -/
@[stacks 0AFX "determinant map on projective K0"]
def det :
    CategoryTheory.ModuleCat.K0.projective.{u, v} R →+
      Additive (CommRing.Pic R) :=
  ObjectProperty.GrothendieckGroup.lift (detClass R) (relations_le_ker_det R)

/-- The determinant map evaluates on a finite-projective generator by its determinant Picard class. -/
@[simp, stacks 0AFX "determinant map on a projective K0 generator"]
theorem det_of (M : ModuleCat.FiniteProjective.{u, v} R) :
    det R (CategoryTheory.ModuleCat.K0.projectiveOf R M) = detClass R M := sorry
-- Proof strategy: unfold `det` and `projectiveOf`, then use the computation rules for
-- `ObjectProperty.GrothendieckGroup.lift` and `FreeAbelianGroup.lift_of`.

end CategoryTheory.ModuleCat.K0.Projective

end
