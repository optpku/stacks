module

public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.HasLimits
public import stacks_project.Chap65.Definition_65_6_3_Hom
public import stacks_project.Chap65.Definition_65_12_1_Subspace
public import stacks_project.Chap65.Definition_65_13_2_Separation
public import stacks_project.Chap66.Definition_66_3_1_Separation
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap66.Definition_66_5_1_QuasiCompact
public import stacks_project.Chap66.Lemma_66_4_8_Opens
public import stacks_project.Chap67.Definition_67_20_2_Affine
public import stacks_project.Chap70.Situation_70_5_5_QcqsAffine

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

/-- A quasi-compact open subspace of a specified directed affine limit of
quasi-compact, absolutely quasi-separated algebraic spaces is the inverse image
of a quasi-compact open subspace at some stage. -/
theorem QcqsAffineLimit.exists_quasiCompactOpen_preimage_eq
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {S : Scheme.{u}} {D : OrderDual I ⥤ AlgebraicSpace S}
    [∀ j, IsQuasiCompact (D.obj j)]
    [∀ j, IsQuasiSeparated (D.obj j)]
    [∀ j, IsAbsolutelyQuasiSeparated (D.obj j)]
    [∀ {j j' : I} (h : j ≤ j'), Affine (D.map (homOfLE h))]
    (s : QcqsAffineLimit D) (U : OpenSubspace s.limitCone.cone.pt)
    [IsQuasiCompact U.X] :
    ∃ i : I, ∃ Ui : OpenSubspace (D.obj i),
      IsQuasiCompact Ui.X ∧
        Points.map (s.limitCone.cone.π.app i) ⁻¹' Ui.pointsSet =
          U.pointsSet := sorry

end AlgebraicGeometry.AlgebraicSpace.Limit
