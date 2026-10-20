module

public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.HasLimits
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.Support

/-!
# Quasi-compact open descent along directed affine limits of algebraic spaces

A quasi-compact open subspace of a specified inverse limit of quasi-compact,
absolutely quasi-separated algebraic spaces with affine transitions is the
inverse image of a quasi-compact open subspace at some stage.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Limit

/-- In a directed inverse system of quasi-compact and absolutely quasi-separated
algebraic spaces with affine transition morphisms, every quasi-compact open
subspace of a specified limit is the inverse image of a quasi-compact open
subspace at some stage. -/
theorem exists_quasiCompactOpen_preimage_eq
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {S : Scheme.{u}} (D : OrderDual I ⥤ AlgebraicSpace S)
    (c : Cone D) (hc : IsLimit c)
    [∀ j, IsQuasiCompact (D.obj j)]
    [∀ j, IsAbsolutelyQuasiSeparated (D.obj j)]
    [∀ {j j' : I} (h : j ≤ j'), Affine (D.map (homOfLE h))]
    (U : OpenSubspace c.pt) [IsQuasiCompact U.X] :
    ∃ i : I, ∃ Ui : OpenSubspace (D.obj i),
      IsQuasiCompact Ui.X ∧
        Points.map (c.π.app i) ⁻¹' Ui.pointsSet = U.pointsSet := sorry

end AlgebraicGeometry.AlgebraicSpace.Limit
