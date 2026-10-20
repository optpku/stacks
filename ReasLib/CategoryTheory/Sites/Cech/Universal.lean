/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Homology.CohomologicalDeltaFunctor.Effaceable
public import ReasLib.CategoryTheory.Homology.CohomologicalDeltaFunctor.LeftExact
public import ReasLib.Algebra.Category.Grp.ExactProducts
public import ReasLib.CategoryTheory.Sites.Cech.DeltaFunctor
import Mathlib.Tactic.CrossRefAttribute

/-!
# Universal Cech delta functors

This leaf owns the universality of Cech cohomology for abelian-group-valued presheaves. The
generic effaceability criterion and degree-zero left-exactness theorem remain in the abstract
cohomological-delta-functor layer.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe w z v u

namespace CategoryTheory.Cech

variable {C : Type u} [Category.{v} C]
variable (U : C) [HasFiniteProducts (Over U)]
variable {ι : Type w} (family : ι → Over U)
variable [HasProducts.{w} AddCommGrpCat.{z}]

/-- Lemma 21.9.6 (Tag 03AU): Cech cohomology of abelian-group-valued presheaves is a universal
cohomological delta functor. -/
@[stacks 03AU "universality of the Cech delta functor"]
noncomputable instance deltaFunctor_isUniversal :
    (deltaFunctor (A := AddCommGrpCat.{z}) U family).IsUniversal := sorry

end CategoryTheory.Cech

namespace CategoryTheory.Cech.FixedTarget

open CategoryTheory CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] {U : C} {ι : Type w}
variable (family : ι → Over U) [HasIteratedFiberProducts family]
variable [HasProducts.{w} AddCommGrpCat.{max u v}]

/-- Lemma 21.9.6 (Tag 03AU): the fixed-target Cech delta functor is universal. -/
@[stacks 03AU "universality of the fixed-target Cech delta functor"]
noncomputable instance deltaFunctor_isUniversal :
    (deltaFunctor family).IsUniversal := sorry

end CategoryTheory.Cech.FixedTarget
