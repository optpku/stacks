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
# Relative affinity descent along directed affine limits of algebraic spaces

If a specified inverse limit of quasi-compact, absolutely quasi-separated algebraic
spaces over a quasi-compact quasi-separated algebraic space, with affine transitions,
is affine over that base, then all sufficiently late stages are affine over the base.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Limit

/-- If the limit-to-base morphism of a directed inverse system of quasi-compact and
absolutely quasi-separated algebraic spaces over a quasi-compact quasi-separated
algebraic space is affine, then the stage-to-base morphisms are affine at every
sufficiently late stage. -/
theorem exists_eventually_isAffine_to_base_of_isLimit
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {S : Scheme.{u}} {Y : AlgebraicSpace S}
    (D : OrderDual I ⥤ AlgebraicSpace S)
    (t : D ⟶ (Functor.const (OrderDual I)).obj Y)
    (c : Cone D) (hc : IsLimit c) (σlim : c.pt ⟶ Y)
    (hπ : c.π ≫ t = (Functor.const _).map σlim)
    [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y]
    [∀ i : I, IsQuasiCompact (D.obj i)]
    [∀ i : I, IsAbsolutelyQuasiSeparated (D.obj i)]
    [∀ {i i' : I} (hii' : i ≤ i'), Affine (D.map (homOfLE hii'))]
    [Affine σlim] :
    ∃ i₀ : I, ∀ ⦃i : I⦄, i₀ ≤ i → Affine (t.app i) := sorry

/-- If the limit-to-base morphism of a directed inverse system of quasi-compact and
absolutely quasi-separated algebraic spaces over a quasi-compact quasi-separated
algebraic space is affine, then some stage-to-base morphism is affine. -/
theorem exists_isAffine_to_base_of_isLimit
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {S : Scheme.{u}} {Y : AlgebraicSpace S}
    (D : OrderDual I ⥤ AlgebraicSpace S)
    (t : D ⟶ (Functor.const (OrderDual I)).obj Y)
    (c : Cone D) (hc : IsLimit c) (σlim : c.pt ⟶ Y)
    (hπ : c.π ≫ t = (Functor.const _).map σlim)
    [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y]
    [∀ i : I, IsQuasiCompact (D.obj i)]
    [∀ i : I, IsAbsolutelyQuasiSeparated (D.obj i)]
    [∀ {i i' : I} (hii' : i ≤ i'), Affine (D.map (homOfLE hii'))]
    [Affine σlim] :
    ∃ i : I, Affine (t.app i) := sorry

end AlgebraicGeometry.AlgebraicSpace.Limit
