module

public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import stacks_project.Chap65.Definition_65_6_3_Hom
public import stacks_project.Chap65.Definition_65_13_2_Separation
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap66.Definition_66_5_1_QuasiCompact
public import stacks_project.Chap67.Definition_67_20_2_Affine

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Limit.MorphismBaseChange

/-!
# Morphisms over a distinguished stage of a directed affine inverse system

The explicit morphism setup and its base changes are provided by their shared
mathematical owner. Historical imports remain available to downstream consumers.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry AlgebraicSpace

noncomputable section

universe u

section

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
variable {S : Scheme.{u}} (D : OrderDual I ⥤ AlgebraicSpace S)
variable (i0 : I) (X0 Y0 : AlgebraicSpace S)
variable [IsQuasiCompact (D.obj i0)] [IsQuasiSeparated (D.obj i0)]
variable [IsQuasiCompact X0] [IsQuasiSeparated X0]
variable [IsQuasiCompact Y0] [IsQuasiSeparated Y0]
variable [∀ {i i' : I} (h : i ≤ i'), Affine (D.map (homOfLE h))]

/- The shared constructor preserves a specified limiting cone and compatible morphisms. -/
#check (AlgebraicGeometry.AlgebraicSpace.Limit.QcqsMorphismBaseChange.ofCone D i0 X0 Y0 :
  ∀ (c : Cone D) (hc : IsLimit c) (x0 : X0 ⟶ D.obj i0)
    (y0 : Y0 ⟶ D.obj i0) (f0 : X0 ⟶ Y0) (hf0 : f0 ≫ y0 = x0),
    AlgebraicGeometry.AlgebraicSpace.Limit.QcqsMorphismBaseChange D i0 X0 Y0)

end
