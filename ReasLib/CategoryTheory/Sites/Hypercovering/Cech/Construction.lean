/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.FormalCoproducts.Cech
public import ReasLib.CategoryTheory.Limits.FormalCoproduct.FiniteLimits
public import ReasLib.CategoryTheory.Limits.Over.FiniteLimits
public import ReasLib.CategoryTheory.Sites.Hypercovering.Constructors
import Mathlib.Tactic.CrossRefAttribute

/-!
# Cech hypercoverings

This leaf constructs the Cech simplicial fixed-target family of a covering family and packages it
as a hypercovering. The construction is independent of the later Cech cohomology API.
-/

@[expose] public section

noncomputable section

universe w v u

namespace CategoryTheory

open Opposite
open Limits
open scoped CategoryTheory.SemiRepresentableFamily

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} [HasPullbacks C]

namespace SemiRepresentableFamily.OverFamily

/-- The degree-zero term of the Cech simplicial object generates the original family sieve. -/
@[simp] theorem cech_zero_toSieve {X : C}
    (𝒰 : SemiRepresentableFamily.OverFamily.{v, u, w} X) :
    ((Limits.FormalCoproduct.cech 𝒰).obj
      (op <| SimplexCategory.mk 0)).toSieve = 𝒰.toSieve := sorry

/-- A covering family gives a covering degree-zero term in its Cech simplicial object. -/
theorem cech_zero_isCovering {X : C}
    (𝒰 : SemiRepresentableFamily.OverFamily.{v, u, w} X)
    (h𝒰 : 𝒰.toSieve ∈ J X) :
    ((Limits.FormalCoproduct.cech 𝒰).obj
      (op <| SimplexCategory.mk 0)).toSieve ∈ J X := sorry

/-- Every higher matching map of a Cech simplicial object is covering. -/
theorem cech_succ_isCovering {X : C}
    (𝒰 : SemiRepresentableFamily.OverFamily.{v, u, w} X) (n : ℕ) :
    SemiRepresentableFamily.OverFamily.covering J
      (SimplicialObject.matchingMap (Limits.FormalCoproduct.cech 𝒰) n) := sorry

end SemiRepresentableFamily.OverFamily

namespace Hypercovering

variable {X : C}

/-- Example 25.3.4 (01G6): the Cech simplicial object of a covering family is a
hypercovering. -/
@[stacks 01G6 "Cech hypercovering"]
noncomputable def cech
    (𝒰 : SemiRepresentableFamily.OverFamily.{v, u, w} X)
    (h𝒰 : 𝒰.toSieve ∈ J X) : Hypercovering.{w} J X :=
  ofSimplicial (Limits.FormalCoproduct.cech 𝒰)
    (SemiRepresentableFamily.OverFamily.cech_zero_isCovering 𝒰 h𝒰)
    (SemiRepresentableFamily.OverFamily.cech_succ_isCovering 𝒰)

/-- The simplicial object underlying a Cech hypercovering is the Cech object of its family. -/
@[simp] theorem cech_toSimplicialObject
    (𝒰 : SemiRepresentableFamily.OverFamily.{v, u, w} X)
    (h𝒰 : 𝒰.toSieve ∈ J X) :
    (cech 𝒰 h𝒰).toSimplicialObject =
      Limits.FormalCoproduct.cech 𝒰 := sorry

/-- Example 25.3.6 (0GMA): a covering arrow gives the Cech hypercovering of its singleton
family. -/
@[stacks 0GMA "Cech hypercovering of a covering arrow"]
noncomputable abbrev cechOfArrow {U : C} (f : U ⟶ X)
    (hf : (SemiRepresentableFamily.OverFamily.singleton.{v, u, w} f).toSieve ∈ J X) :
    Hypercovering.{w} J X :=
  cech (SemiRepresentableFamily.OverFamily.singleton.{v, u, w} f) hf

end Hypercovering

end CategoryTheory
