/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Field.Basic
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Over
public import stacks_project.Chap65.Definition_65_13_2_Separation
public import stacks_project.Chap65.Lemma_65_6_2_OfOver
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Lemma_67_24_2_FieldPoints
public import stacks_project.Chap78.Definition_78_5_1_Group

/-!
# No rational curves on group algebraic spaces

A separated group algebraic space locally of finite type over a field admits
no nonconstant morphism from the projective line over that field.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism of algebraic spaces over `S` is constant if it factors through
the unique morphism `toBase X` from `X` to `S` as an algebraic space over
itself. -/
def IsConstant {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) : Prop :=
  ∃ g : ofOver (Over.mk (𝟙 S)) ⟶ Y, toBase X ≫ g = f

/-- `IsConstant f` holds if and only if `f` factors through `toBase X`. -/
theorem isConstant_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    IsConstant f ↔ ∃ g : ofOver (Over.mk (𝟙 S)) ⟶ Y, toBase X ≫ g = f :=
  sorry

/-- The composite of `toBase X` with a morphism out of the base is constant. -/
theorem isConstant_comp_toBase {S : Scheme.{u}} {Y : AlgebraicSpace S}
    (X : AlgebraicSpace S) (g : ofOver (Over.mk (𝟙 S)) ⟶ Y) :
    IsConstant (toBase X ≫ g) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace

namespace AlgebraicGeometry.GroupAlgebraicSpace

/-- Lemma 79.11.3: Let `k` be a field. Let `G` be a separated group algebraic
space locally of finite type over `k`. There does not exist a nonconstant
morphism `f : P¹_k ⟶ G` over `Spec k`.

Here `P¹_k` is the algebraic space `ofOver (ProjectiveSpace.schemeOver k 1)`,
morphisms over `Spec k` are morphisms of algebraic spaces over
`Spec (CommRingCat.of k)`, and a morphism is constant when it is
`AlgebraicSpace.IsConstant`. -/
@[stacks 0AEN]
theorem isConstant_hom_projectiveLine {k : Type u} [Field k]
    (G : GroupAlgebraicSpace (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k))))))
    [AlgebraicSpace.IsSeparated G.X.left]
    [AlgebraicSpace.LocallyOfFiniteType (toBase G.X.left)]
    (f : ofOver (ProjectiveSpace.schemeOver k 1) ⟶ G.X.left) :
    AlgebraicSpace.IsConstant f :=
  sorry

/-- There is no nonconstant morphism from `P¹_k` to a separated group algebraic
space locally of finite type over a field `k`. -/
theorem not_exists_not_isConstant_hom_projectiveLine {k : Type u} [Field k]
    (G : GroupAlgebraicSpace (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k))))))
    [AlgebraicSpace.IsSeparated G.X.left]
    [AlgebraicSpace.LocallyOfFiniteType (toBase G.X.left)] :
    ¬ ∃ f : ofOver (ProjectiveSpace.schemeOver k 1) ⟶ G.X.left,
        ¬ AlgebraicSpace.IsConstant f :=
  sorry

end AlgebraicGeometry.GroupAlgebraicSpace
