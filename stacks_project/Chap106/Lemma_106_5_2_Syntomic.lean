/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Lemma_67_36_4_Syntomic
public import stacks_project.Chap101.Lemma_101_25_5_Flat

/-!
# Syntomic morphisms of algebraic stacks

A morphism of algebraic stacks is syntomic when some (equivalently, any) smooth
algebraic-space presentation square with surjective source atlas has syntomic
top arrow, in parallel with `AlgebraicStack.Smooth` and `AlgebraicStack.Flat`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- A morphism `f : X ⟶ Y` of algebraic stacks over `S` is syntomic if some
commutative square with algebraic-space vertices, smooth vertical arrows, and
surjective source atlas has syntomic top arrow. -/
class Syntomic {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) : Prop where
  /-- There is a smooth presentation of `f` by algebraic spaces whose source
  atlas is surjective and whose top arrow is syntomic. -/
  exists_surjective_smooth_presentation :
    ∃ (U V : AlgebraicSpace S) (a : U.toGroupoids ⟶ X) (b : V.toGroupoids ⟶ Y)
      (h : U ⟶ V),
      IsSmoothSurjectivePresentation f a b h ∧ AlgebraicSpace.Syntomic h

/-- A morphism of algebraic stacks is syntomic if and only if it admits a
smooth algebraic-space presentation with surjective source atlas and syntomic
top arrow. -/
theorem syntomic_iff {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    Syntomic f ↔
      ∃ (U V : AlgebraicSpace S) (a : U.toGroupoids ⟶ X) (b : V.toGroupoids ⟶ Y)
        (h : U ⟶ V),
        IsSmoothSurjectivePresentation f a b h ∧ AlgebraicSpace.Syntomic h :=
  sorry

namespace Syntomic

/-- The identity morphism of an algebraic stack is syntomic. -/
instance id {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] :
    Syntomic (𝟙 X) :=
  sorry

/-- A syntomic morphism of algebraic stacks admits a smooth algebraic-space
presentation with surjective source atlas and syntomic top arrow. -/
theorem spec {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Syntomic f] :
    ∃ (U V : AlgebraicSpace S) (a : U.toGroupoids ⟶ X) (b : V.toGroupoids ⟶ Y)
      (h : U ⟶ V),
      IsSmoothSurjectivePresentation f a b h ∧ AlgebraicSpace.Syntomic h :=
  sorry

end Syntomic

end AlgebraicGeometry.AlgebraicStack
