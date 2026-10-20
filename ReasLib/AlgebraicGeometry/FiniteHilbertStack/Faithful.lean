/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FiniteHilbertStack.Forgetful

/-!
# Faithfulness of the finite Hilbert forgetful morphism

The forgetful 1-morphism `ℋ_d(𝒳/𝒴) ⟶ ℋ_d(𝒳)` is faithful on total and
fibre categories for positive degree.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open StackOver.Groupoids.Hom
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.FiniteHilbertStack

variable {S : Scheme.{u}}
variable {𝒳 𝒴 : StackOver.Groupoids.{u + 1, u, u + 1, u} (Scheme.fppfTopology.over S)}

/-- For positive degree, the forgetful 1-morphism `ℋ_d(𝒳/𝒴) ⟶ ℋ_d(𝒳)` is
faithful on every fibre category over `(Sch/S)_fppf`. -/
instance forgetToAbsolute.fiberwiseFaithful (F : 𝒳 ⟶ 𝒴) (d : ℕ) [NeZero d] (U : Over S) :
    (fiberFunctor (forgetToAbsolute F d) U).Faithful := sorry

/-- For positive degree, the forgetful 1-morphism `ℋ_d(𝒳/𝒴) ⟶ ℋ_d(𝒳)` of
stacks in groupoids over `(Sch/S)_fppf` is faithful. -/
@[stacks 05XV]
instance forgetToAbsolute.faithful (F : 𝒳 ⟶ 𝒴) (d : ℕ) [NeZero d] :
    (toBasedFunctor (forgetToAbsolute F d)).Faithful := sorry

end AlgebraicGeometry.FiniteHilbertStack
