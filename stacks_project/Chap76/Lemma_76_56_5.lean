module

public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.HasLimits
public import stacks_project.Chap66.Definition_66_3_1_Separation
public import stacks_project.Chap66.Definition_66_5_1_QuasiCompact
public import stacks_project.Chap67.Definition_67_20_2_Affine
public import stacks_project.Chap75.Definition_75_28_1_ResolutionProperty

/-!
# Resolution property of directed affine limits of algebraic spaces

A specified inverse limit of quasi-compact, absolutely quasi-separated algebraic
spaces over a scheme with affine transition morphisms has the resolution property
if and only if some stage does.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Limit

/-- Lemma 76.56.5: a specified inverse limit of quasi-compact and quasi-separated
algebraic spaces over a scheme `S` with affine transition morphisms has the
resolution property if and only if some stage does. -/
@[stacks 0GV2]
theorem hasResolutionProperty_iff_exists_stage
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {S : Scheme.{u}} (D : OrderDual I ⥤ AlgebraicSpace S)
    (c : Cone D) (hc : IsLimit c)
    [∀ i, IsQuasiCompact (D.obj i)]
    [∀ i, IsAbsolutelyQuasiSeparated (D.obj i)]
    [∀ {i i' : I} (hii' : i ≤ i'), Affine (D.map (homOfLE hii'))] :
    HasResolutionProperty c.pt ↔ ∃ i : I, HasResolutionProperty (D.obj i) := sorry

end AlgebraicGeometry.AlgebraicSpace.Limit
