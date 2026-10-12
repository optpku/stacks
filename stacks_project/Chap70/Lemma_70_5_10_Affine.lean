/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.HasLimits
public import stacks_project.Chap65.Definition_65_6_3_Hom
public import stacks_project.Chap66.Definition_66_3_1_Separation
public import stacks_project.Chap66.Definition_66_5_1_QuasiCompact
public import stacks_project.Chap67.Definition_67_20_2_Affine

/-!
# Affineness descent along directed affine limits of algebraic spaces

If a specified inverse limit of quasi-compact, absolutely quasi-separated algebraic
spaces with affine transitions is affine, then all sufficiently late stages are
affine.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Limit

/-- In a directed inverse system of quasi-compact and absolutely quasi-separated
algebraic spaces with affine transition morphisms, if a specified limit is
affine, then all sufficiently late stages are affine. -/
theorem exists_eventually_isAffine_of_isLimit
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {S : Scheme.{u}} (D : OrderDual I ⥤ AlgebraicSpace S)
    (c : Cone D) (hc : IsLimit c)
    [∀ j, IsQuasiCompact (D.obj j)]
    [∀ j, IsAbsolutelyQuasiSeparated (D.obj j)]
    [∀ {j j' : I} (hjj' : j ≤ j'), Affine (D.map (homOfLE hjj'))]
    [AlgebraicSpace.IsAffine c.pt] :
    ∃ i₀ : I, ∀ ⦃i : I⦄, i₀ ≤ i → AlgebraicSpace.IsAffine (D.obj i) := sorry

/-- If a specified inverse limit of quasi-compact and absolutely quasi-separated
algebraic spaces with affine transition morphisms is affine, then some stage is
affine. -/
theorem exists_isAffine_of_isLimit
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {S : Scheme.{u}} (D : OrderDual I ⥤ AlgebraicSpace S)
    (c : Cone D) (hc : IsLimit c)
    [∀ j, IsQuasiCompact (D.obj j)]
    [∀ j, IsAbsolutelyQuasiSeparated (D.obj j)]
    [∀ {j j' : I} (hjj' : j ≤ j'), Affine (D.map (homOfLE hjj'))]
    [AlgebraicSpace.IsAffine c.pt] :
    ∃ i : I, AlgebraicSpace.IsAffine (D.obj i) := sorry

end AlgebraicGeometry.AlgebraicSpace.Limit
