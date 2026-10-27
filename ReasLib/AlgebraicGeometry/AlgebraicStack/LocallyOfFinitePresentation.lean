/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocallyOfFinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicStack.SmoothPresentation
public import ReasLib.AlgebraicGeometry.GroupoidsOver.LocallyOfFinitePresentation

/-!
# Locally of finite presentation for morphisms of algebraic stacks

A morphism of algebraic stacks is locally of finite presentation when some
smooth algebraic-space presentation square with surjective source atlas has
locally-of-finite-presentation top arrow, parallel to `AlgebraicStack.Flat`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- A morphism `f : X ⟶ Y` of algebraic stacks over `S` is locally of finite
presentation if some commutative square with algebraic-space vertices, smooth
vertical arrows, and surjective source atlas has locally-of-finite-presentation
top arrow. -/
class LocallyOfFinitePresentation {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) : Prop where
  /-- There is a smooth presentation of `f` by algebraic spaces whose source
  atlas is surjective and whose top arrow is locally of finite presentation. -/
  exists_surjective_smooth_presentation :
    ∃ (U V : AlgebraicSpace S) (a : U.toGroupoids ⟶ X) (b : V.toGroupoids ⟶ Y)
      (h : U ⟶ V),
      IsSmoothSurjectivePresentation f a b h ∧
        AlgebraicSpace.LocallyOfFinitePresentation h

/-- A morphism of algebraic stacks is locally of finite presentation if and only
if it admits a smooth algebraic-space presentation with surjective source atlas
and locally-of-finite-presentation top arrow. -/
theorem locallyOfFinitePresentation_iff {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    LocallyOfFinitePresentation f ↔
      ∃ (U V : AlgebraicSpace S) (a : U.toGroupoids ⟶ X) (b : V.toGroupoids ⟶ Y)
        (h : U ⟶ V),
        IsSmoothSurjectivePresentation f a b h ∧
          AlgebraicSpace.LocallyOfFinitePresentation h :=
  sorry

namespace LocallyOfFinitePresentation

/-- Representable local finite presentation implies local finite presentation
as a morphism of algebraic stacks.

Stacks, Tag 06Q2 and the preceding compatibility paragraph:
`source/stacks-official-a04446e57ec1/additional-sources-2.md:32226-32257`. -/
instance of_groupoidsHom {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [Groupoids.Hom.LocallyOfFinitePresentation f] : LocallyOfFinitePresentation f where
  exists_surjective_smooth_presentation := by
    sorry

/-- For a morphism of algebraic stacks representable by algebraic spaces,
local finite presentation agrees with representable local finite presentation.

Stacks, Tags 06Q2 and 06FM:
`source/stacks-official-a04446e57ec1/additional-sources-2.md:32226-32257`
and `additional-sources-2.md:29887-29917` in the same source directory. -/
theorem iff_groupoidsHom {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    (hf : relativelyRepresentableByAlgebraicSpaces f) :
    LocallyOfFinitePresentation f ↔ Groupoids.Hom.LocallyOfFinitePresentation f := by
  constructor
  · intro h
    apply (Groupoids.Hom.LocallyOfFinitePresentation.iff_has f hf).mpr
    sorry
  · intro h
    letI := h
    exact of_groupoidsHom f

/-- The identity morphism of an algebraic stack is locally of finite
presentation. -/
instance id {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] :
    LocallyOfFinitePresentation (𝟙 X) :=
  sorry

/-- A locally-of-finite-presentation morphism of algebraic stacks admits a
smooth algebraic-space presentation with surjective source atlas and
locally-of-finite-presentation top arrow. -/
theorem spec {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [LocallyOfFinitePresentation f] :
    ∃ (U V : AlgebraicSpace S) (a : U.toGroupoids ⟶ X) (b : V.toGroupoids ⟶ Y)
      (h : U ⟶ V),
      IsSmoothSurjectivePresentation f a b h ∧
        AlgebraicSpace.LocallyOfFinitePresentation h :=
  sorry

/-- A morphism of algebraic spaces that is locally of finite presentation
induces a 1-morphism of algebraic stacks that is locally of finite
presentation. -/
instance of_toGroupoids {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [AlgebraicSpace.LocallyOfFinitePresentation f] :
    LocallyOfFinitePresentation (AlgebraicSpace.toGroupoids.map f) :=
  sorry

end LocallyOfFinitePresentation

end AlgebraicGeometry.AlgebraicStack
