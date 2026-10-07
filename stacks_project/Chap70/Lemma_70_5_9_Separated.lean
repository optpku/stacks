module

public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.HasLimits
public import stacks_project.Chap65.Definition_65_6_3_Hom
public import stacks_project.Chap66.Definition_66_3_1_Separation
public import stacks_project.Chap66.Definition_66_5_1_QuasiCompact
public import stacks_project.Chap67.Definition_67_20_2_Affine

/-!
# Absolute separatedness descent along directed affine limits of algebraic spaces

If a specified inverse limit of quasi-compact, absolutely quasi-separated algebraic
spaces with affine transitions is absolutely separated, then all sufficiently late
stages are absolutely separated.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Limit

/-- In a directed inverse system of quasi-compact and absolutely quasi-separated
algebraic spaces with affine transition morphisms, if a specified limit is
absolutely separated, then all sufficiently late stages are absolutely
separated. -/
theorem exists_eventually_isSeparated_of_isLimit
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {S : Scheme.{u}} (D : OrderDual I ⥤ AlgebraicSpace S)
    (c : Cone D) (hc : IsLimit c)
    [∀ j, IsQuasiCompact (D.obj j)]
    [∀ j, IsAbsolutelyQuasiSeparated (D.obj j)]
    [∀ {j j' : I} (hjj' : j ≤ j'), Affine (D.map (homOfLE hjj'))]
    [IsAbsolutelySeparated c.pt] :
    ∃ i₀ : I, ∀ ⦃i : I⦄, i₀ ≤ i → IsAbsolutelySeparated (D.obj i) := sorry

/-- If a specified inverse limit of quasi-compact and absolutely quasi-separated
algebraic spaces with affine transition morphisms is absolutely separated, then
some stage is absolutely separated. -/
theorem exists_isSeparated_of_isLimit
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {S : Scheme.{u}} (D : OrderDual I ⥤ AlgebraicSpace S)
    (c : Cone D) (hc : IsLimit c)
    [∀ j, IsQuasiCompact (D.obj j)]
    [∀ j, IsAbsolutelyQuasiSeparated (D.obj j)]
    [∀ {j j' : I} (hjj' : j ≤ j'), Affine (D.map (homOfLE hjj'))]
    [IsAbsolutelySeparated c.pt] :
    ∃ i : I, IsAbsolutelySeparated (D.obj i) := sorry

end AlgebraicGeometry.AlgebraicSpace.Limit
