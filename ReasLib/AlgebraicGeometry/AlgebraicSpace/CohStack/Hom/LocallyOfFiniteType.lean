/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Hom.Presentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Algebraic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType

/-!
# Locally finite type morphisms of lifted groupoid fibrations
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.GroupScheme
open FiberedCategoryOver
open AlgebraicGeometry.AlgebraicSpace.CohStack (AlgebraicStack)
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.CohStack.Hom

/-- A 1-morphism `f : X ⟶ Y` of categories fibred in groupoids over `Over S`, in
the Hom-universe of `CohStack.toGroupoids`, is locally of finite type if some
commutative square with algebraic-space vertices, smooth vertical arrows, and
surjective source atlas has locally-of-finite-type top arrow. -/
class LocallyOfFiniteType {S : Scheme.{u}}
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    (f : X ⟶ Y) : Prop where
  /-- There is a smooth presentation of `f` by algebraic spaces whose source
  atlas is surjective and whose top arrow is locally of finite type. -/
  exists_surjective_smooth_presentation :
    ∃ (U V : AlgebraicSpace S) (a : Classifying.toGroupoids U ⟶ X)
      (b : Classifying.toGroupoids V ⟶ Y) (h : U ⟶ V),
      IsSmoothSurjectivePresentation f a b h ∧
        AlgebraicSpace.LocallyOfFiniteType h

/-- A 1-morphism is locally of finite type if and only if it admits a smooth
algebraic-space presentation with surjective source atlas and
locally-of-finite-type top arrow. -/
theorem locallyOfFiniteType_iff {S : Scheme.{u}}
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    (f : X ⟶ Y) :
    LocallyOfFiniteType f ↔
      ∃ (U V : AlgebraicSpace S) (a : Classifying.toGroupoids U ⟶ X)
        (b : Classifying.toGroupoids V ⟶ Y) (h : U ⟶ V),
        IsSmoothSurjectivePresentation f a b h ∧
          AlgebraicSpace.LocallyOfFiniteType h :=
  sorry

namespace LocallyOfFiniteType

/-- The identity 1-morphism of an algebraic stack is locally of finite type. -/
instance id {S : Scheme.{u}}
    {X : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    [AlgebraicStack X] : LocallyOfFiniteType (𝟙 X) :=
  sorry

/-- A morphism of algebraic spaces that is locally of finite type induces a
1-morphism of categories fibred in groupoids that is locally of finite type. -/
instance of_toGroupoids {S : Scheme.{u}} {U V : AlgebraicSpace S} (h : U ⟶ V)
    [AlgebraicSpace.LocallyOfFiniteType h] :
    LocallyOfFiniteType (Classifying.toGroupoids.map h) :=
  sorry

/-- A locally-of-finite-type 1-morphism admits a smooth algebraic-space
presentation with surjective source atlas and locally-of-finite-type top
arrow. -/
theorem spec {S : Scheme.{u}}
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    (f : X ⟶ Y) [LocallyOfFiniteType f] :
    ∃ (U V : AlgebraicSpace S) (a : Classifying.toGroupoids U ⟶ X)
      (b : Classifying.toGroupoids V ⟶ Y) (h : U ⟶ V),
      IsSmoothSurjectivePresentation f a b h ∧
        AlgebraicSpace.LocallyOfFiniteType h :=
  sorry

end LocallyOfFiniteType

end AlgebraicGeometry.AlgebraicSpace.CohStack.Hom
