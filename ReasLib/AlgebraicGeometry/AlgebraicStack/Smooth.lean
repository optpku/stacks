/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.SmoothPresentation
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Smooth

/-!
# Smooth morphisms of algebraic stacks

A morphism of algebraic stacks is smooth when some (equivalently, any) smooth
algebraic-space presentation square with surjective source atlas has smooth top
arrow, in parallel with `AlgebraicStack.Flat`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- A morphism `f : X ⟶ Y` of algebraic stacks over `S` is smooth if some
commutative square with algebraic-space vertices, smooth vertical arrows, and
surjective source atlas has smooth top arrow. -/
class Smooth {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) : Prop where
  /-- There is a smooth presentation of `f` by algebraic spaces whose source
  atlas is surjective and whose top arrow is smooth. -/
  exists_surjective_smooth_presentation :
    ∃ (U V : AlgebraicSpace S) (a : U.toGroupoids ⟶ X) (b : V.toGroupoids ⟶ Y)
      (h : U ⟶ V),
      IsSmoothSurjectivePresentation f a b h ∧ AlgebraicSpace.Smooth h

/-- A morphism of algebraic stacks is smooth if and only if it admits a smooth
algebraic-space presentation with surjective source atlas and smooth top
arrow. -/
theorem smooth_iff {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    Smooth f ↔
      ∃ (U V : AlgebraicSpace S) (a : U.toGroupoids ⟶ X) (b : V.toGroupoids ⟶ Y)
        (h : U ⟶ V),
        IsSmoothSurjectivePresentation f a b h ∧ AlgebraicSpace.Smooth h :=
  sorry

namespace Smooth

/-- Representable smoothness implies smoothness as a morphism of algebraic stacks.

Stacks, Tag 075U and the preceding compatibility paragraph:
`source/stacks-official-a04446e57ec1/additional-sources-2.md:34224-34248`. -/
instance of_groupoidsHom {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [Groupoids.Hom.Smooth f] : Smooth f where
  exists_surjective_smooth_presentation := by
    sorry

/-- For a morphism of algebraic stacks representable by algebraic spaces,
smoothness agrees with representable smoothness.

Stacks, Tags 075U and 06FM:
`source/stacks-official-a04446e57ec1/additional-sources-2.md:34224-34248`
and `additional-sources-2.md:29887-29917` in the same source directory. -/
theorem iff_groupoidsHom {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    (hf : relativelyRepresentableByAlgebraicSpaces f) :
    Smooth f ↔ Groupoids.Hom.Smooth f := by
  constructor
  · intro h
    apply (Groupoids.Hom.Smooth.iff_has f hf).mpr
    sorry
  · intro h
    letI := h
    exact of_groupoidsHom f

/-- The identity morphism of an algebraic stack is smooth. -/
instance id {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] :
    Smooth (𝟙 X) :=
  sorry

/-- A smooth morphism of algebraic stacks admits a smooth algebraic-space
presentation with surjective source atlas and smooth top arrow. -/
theorem spec {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Smooth f] :
    ∃ (U V : AlgebraicSpace S) (a : U.toGroupoids ⟶ X) (b : V.toGroupoids ⟶ Y)
      (h : U ⟶ V),
      IsSmoothSurjectivePresentation f a b h ∧ AlgebraicSpace.Smooth h :=
  sorry

end Smooth

end AlgebraicGeometry.AlgebraicStack
