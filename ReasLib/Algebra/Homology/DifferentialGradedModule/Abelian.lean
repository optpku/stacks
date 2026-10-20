/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Abelian.Basic
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Limits

/-!
# The Abelian Category of Differential Graded Modules

The additive structure is the explicit degreewise structure already owned by
`DifferentialGradedModule.Preadditive`; only the exact-category laws are deferred here.
-/

@[expose] public section

noncomputable section

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R]

/-- Lemma 22.4.2 (09JJ) (1): right differential graded modules over `A` form an abelian
category.  Its preadditive data is the canonical degreewise structure. -/
@[stacks 09JJ "abelian category of differential graded modules"]
instance abelian (A : CochainDGAlgebra.{u, v} R) :
    Abelian (DifferentialGradedModule.{u, w} A) where
  toPreadditive := instPreadditive A
  toIsNormalMonoCategory := sorry
  toIsNormalEpiCategory := sorry
  has_finite_products := inferInstance
  has_kernels := inferInstance
  has_cokernels := inferInstance

end DifferentialGradedModule
