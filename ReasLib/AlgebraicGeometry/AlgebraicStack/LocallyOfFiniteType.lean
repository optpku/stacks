/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicStack.SmoothPresentation
public import ReasLib.AlgebraicGeometry.GroupoidsOver.LocallyOfFiniteType

/-!
# Locally of finite type for morphisms of algebraic stacks

A morphism of algebraic stacks is locally of finite type when some smooth
algebraic-space presentation square with surjective source atlas has
locally-of-finite-type top arrow, parallel to `AlgebraicStack.Flat`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- A morphism `f : X ⟶ Y` of algebraic stacks over `S` is locally of finite
type if some commutative square with algebraic-space vertices, smooth
vertical arrows, and surjective source atlas has locally-of-finite-type
top arrow. -/
class LocallyOfFiniteType {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) : Prop where
  /-- There is a smooth presentation of `f` by algebraic spaces whose source
  atlas is surjective and whose top arrow is locally of finite type. -/
  exists_surjective_smooth_presentation :
    ∃ (U V : AlgebraicSpace S) (a : U.toGroupoids ⟶ X) (b : V.toGroupoids ⟶ Y)
      (h : U ⟶ V),
      IsSmoothSurjectivePresentation f a b h ∧
        AlgebraicSpace.LocallyOfFiniteType h

/-- A morphism of algebraic stacks is locally of finite type if and only
if it admits a smooth algebraic-space presentation with surjective source atlas
and locally-of-finite-type top arrow. -/
theorem locallyOfFiniteType_iff {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    LocallyOfFiniteType f ↔
      ∃ (U V : AlgebraicSpace S) (a : U.toGroupoids ⟶ X) (b : V.toGroupoids ⟶ Y)
        (h : U ⟶ V),
        IsSmoothSurjectivePresentation f a b h ∧
          AlgebraicSpace.LocallyOfFiniteType h :=
  ⟨fun h ↦ h.exists_surjective_smooth_presentation, fun h ↦ ⟨h⟩⟩

namespace LocallyOfFiniteType

/-- Representable local finite type implies local finite type as a morphism of
algebraic stacks.

Stacks, Tag 06FS and the preceding compatibility paragraph:
`source/stacks-official-a04446e57ec1/additional-sources-2.md:30104-30134`. -/
instance of_groupoidsHom {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [Groupoids.Hom.LocallyOfFiniteType f] : LocallyOfFiniteType f where
  exists_surjective_smooth_presentation := by
    sorry

/-- For a morphism of algebraic stacks representable by algebraic spaces,
local finite type agrees with representable local finite type.

Stacks, Tags 06FS and 06FM:
`source/stacks-official-a04446e57ec1/additional-sources-2.md:30104-30134`
and `additional-sources-2.md:29887-29917` in the same source directory. -/
theorem iff_groupoidsHom {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    (hf : relativelyRepresentableByAlgebraicSpaces f) :
    LocallyOfFiniteType f ↔ Groupoids.Hom.LocallyOfFiniteType f := by
  constructor
  · intro h
    apply (Groupoids.Hom.LocallyOfFiniteType.iff_has f hf).mpr
    sorry
  · intro h
    letI := h
    exact of_groupoidsHom f

/-- The identity morphism of an algebraic stack is locally of finite type. -/
instance id {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] :
    LocallyOfFiniteType (𝟙 X) :=
  of_groupoidsHom (𝟙 X)

/-- A locally-of-finite-type morphism of algebraic stacks admits a smooth
algebraic-space presentation with surjective source atlas and
locally-of-finite-type top arrow. -/
theorem spec {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [LocallyOfFiniteType f] :
    ∃ (U V : AlgebraicSpace S) (a : U.toGroupoids ⟶ X) (b : V.toGroupoids ⟶ Y)
      (h : U ⟶ V),
      IsSmoothSurjectivePresentation f a b h ∧
        AlgebraicSpace.LocallyOfFiniteType h :=
  LocallyOfFiniteType.exists_surjective_smooth_presentation (f := f)

/-- A morphism of algebraic spaces that is locally of finite type induces a
1-morphism of algebraic stacks that is locally of finite type. -/
instance of_toGroupoids {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [AlgebraicSpace.LocallyOfFiniteType f] :
    LocallyOfFiniteType (AlgebraicSpace.toGroupoids.map f) where
  exists_surjective_smooth_presentation := by
    refine ⟨X, Y, 𝟙 X.toGroupoids, 𝟙 Y.toGroupoids, f, ?_, inferInstance⟩
    refine ⟨inferInstance, inferInstance, inferInstance, ?_⟩
    exact ⟨(λ_ (AlgebraicSpace.toGroupoids.map f)) ≪≫
      (ρ_ (AlgebraicSpace.toGroupoids.map f)).symm⟩

end LocallyOfFiniteType

end AlgebraicGeometry.AlgebraicStack
