/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import Mathlib.CategoryTheory.ObjectProperty.Small
public import stacks_project.Chap95.Lemma_95_14_2_Restriction
public import stacks_project.Chap95.Lemma_95_14_2_Torsors

/-!
# Lemma 95.14.2

The functor `p : 𝒢-Torsors ⟶ (Sch/S)_fppf` is a stack in groupoids, up to the
small-fiber replacement of Remark 8.4.9.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.SheafTorsors

variable {S : Scheme.{u}}

/-- Lemma 95.14.2: up to a replacement as in Remark 8.4.9, the functor
`p : 𝒢-Torsors ⟶ (Sch/S)_fppf` sending `(U, ℱ)` to `U` is a stack in groupoids
over `(Sch/S)_fppf`. -/
@[stacks 04UK]
instance isStackInGroupoids (𝒢 : Sheaf (Scheme.fppfTopology.over S) GrpCat.{u}) :
    IsStack.InGroupoids (Scheme.fppfTopology.over S) (forget 𝒢) := sorry

/-- The stack in groupoids of `𝒢`-torsors over `(Sch/S)_fppf`. -/
def stack (𝒢 : Sheaf (Scheme.fppfTopology.over S) GrpCat.{u}) :
    StackOver.Groupoids (Scheme.fppfTopology.over S) :=
  StackOver.Groupoids.ofProjection (Scheme.fppfTopology.over S) (forget 𝒢)

/-- The projection of `stack` is the forgetful functor to `(Sch/S)_fppf`. -/
theorem stack_p (𝒢 : Sheaf (Scheme.fppfTopology.over S) GrpCat.{u}) :
    (stack 𝒢).p = forget 𝒢 := sorry

/-- Remark 8.4.9 condition (4): the fibre of `𝒢`-Torsors over `U` is essentially
small, so a small model exists via `StackOver.SmallModel`. -/
theorem fibers_essentiallySmall (𝒢 : Sheaf (Scheme.fppfTopology.over S) GrpCat.{u})
    (U : Over S) :
    ObjectProperty.EssentiallySmall.{u}
      (⊤ : ObjectProperty ((forget 𝒢).Fiber U)) := sorry

end AlgebraicGeometry.SheafTorsors
