/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Hom.FullyFaithfulComparison
public import ReasLib.CategoryTheory.Fibered.Groupoids.Diagonal.Construction

/-!
# Limit preservation of the diagonal

The diagonal of a 1-morphism of categories fibred in groupoids over
`(Sch/S)_fppf` is limit preserving if and only if the fibre-category
comparison along directed affine inverse limits is fully faithful. In
particular, limit preservation of `p` implies limit preservation of
`Hom.diagonal p`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids hiding diagonal
open FiberedCategoryOver.Groupoids.Hom (diagonal)
open AlgebraicGeometry.Groupoids.Hom
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.Groupoids.Hom

namespace diagonal

/-- Let `p : 𝒳 ⟶ 𝒴` be a 1-morphism of categories fibred in
groupoids over `(Sch/S)_fppf`. The diagonal
`Hom.diagonal p : 𝒳 ⟶ 𝒳 ×_𝒴 𝒳` is limit preserving if and only if for every
directed inverse limit `U = lim U_i` of affine schemes over `S` the functor
`colim 𝒳_{U_i} ⟶ 𝒳_U ×_{𝒴_U} colim 𝒴_{U_i}` is fully faithful. -/
@[stacks 0CMW]
theorem limitPreserving_iff {S : Scheme.{u}} {X Y : GroupoidsOver S} (p : X ⟶ Y) :
    LimitPreserving (diagonal.{u + 1, u, u + 1} p) ↔
      FullyFaithfulComparison p := sorry

/-- If `p : 𝒳 ⟶ 𝒴` is limit preserving, then
so is the diagonal `Hom.diagonal p`. -/
@[stacks 0CMW]
instance limitPreserving {S : Scheme.{u}} {X Y : GroupoidsOver S} (p : X ⟶ Y)
    [LimitPreserving p] :
    LimitPreserving (diagonal.{u + 1, u, u + 1} p) :=
  sorry

end diagonal

end AlgebraicGeometry.Groupoids.Hom
