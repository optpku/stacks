/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Hom.Presentation

/-!
# Smooth morphisms of lifted groupoid fibrations
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.GroupScheme
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.CohStack.Hom

/-- A 1-morphism `f : X ⟶ Y` of categories fibred in groupoids over `Over S`, in
the Hom-universe of `CohStack.toGroupoids`, is smooth if some commutative square
with algebraic-space vertices, smooth vertical arrows, and surjective source
atlas has smooth top arrow. -/
@[stacks 075U]
class Smooth {S : Scheme.{u}}
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    (f : X ⟶ Y) : Prop where
  /-- There is a smooth presentation of `f` by algebraic spaces whose source
  atlas is surjective and whose top arrow is smooth. -/
  exists_surjective_smooth_presentation :
    ∃ (U V : AlgebraicSpace S) (a : Classifying.toGroupoids U ⟶ X)
      (b : Classifying.toGroupoids V ⟶ Y) (h : U ⟶ V),
      IsSmoothSurjectivePresentation f a b h ∧ AlgebraicSpace.Smooth h

/-- A 1-morphism is smooth if and only if it admits a smooth algebraic-space
presentation with surjective source atlas and smooth top arrow. -/
theorem smooth_iff {S : Scheme.{u}}
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    (f : X ⟶ Y) :
    Smooth f ↔
      ∃ (U V : AlgebraicSpace S) (a : Classifying.toGroupoids U ⟶ X)
        (b : Classifying.toGroupoids V ⟶ Y) (h : U ⟶ V),
        IsSmoothSurjectivePresentation f a b h ∧ AlgebraicSpace.Smooth h :=
  sorry

namespace Smooth

/-- The identity of a groupoid fibration admitting a smooth surjective algebraic-space
atlas is smooth. -/
theorem id {S : Scheme.{u}}
    {X : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    (U : AlgebraicSpace S) (a : Classifying.toGroupoids U ⟶ X)
    (ha : Classifying.Smooth a) (hasurj : Classifying.Surjective a) :
    Smooth (𝟙 X) :=
  sorry

/-- A smooth morphism of algebraic spaces induces a smooth 1-morphism of
categories fibred in groupoids. -/
instance of_toGroupoids {S : Scheme.{u}} {U V : AlgebraicSpace S} (h : U ⟶ V)
    [AlgebraicSpace.Smooth h] :
    Smooth (Classifying.toGroupoids.map h) :=
  sorry

/-- On morphisms of algebraic spaces, smoothness of the associated groupoid
fibration morphism is the usual smoothness property. -/
theorem toGroupoids_iff {S : Scheme.{u}} {U V : AlgebraicSpace S} (h : U ⟶ V) :
    Smooth (Classifying.toGroupoids.map h) ↔ AlgebraicSpace.Smooth h :=
  sorry

/-- For a representable morphism whose target admits a smooth surjective atlas,
the presentation criterion agrees with smoothness of every representing base change. -/
theorem iff_classifying {S : Scheme.{u}}
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    (f : X ⟶ Y) (hf : Classifying.relativelyRepresentableByAlgebraicSpaces f)
    (V : AlgebraicSpace S) (b : Classifying.toGroupoids V ⟶ Y)
    (hb : Classifying.Smooth b) (hbsurj : Classifying.Surjective b) :
    Smooth f ↔ Classifying.Smooth f :=
  sorry

/-- A smooth 1-morphism admits a smooth algebraic-space presentation with
surjective source atlas and smooth top arrow. -/
theorem spec {S : Scheme.{u}}
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    (f : X ⟶ Y) [Smooth f] :
    ∃ (U V : AlgebraicSpace S) (a : Classifying.toGroupoids U ⟶ X)
      (b : Classifying.toGroupoids V ⟶ Y) (h : U ⟶ V),
      IsSmoothSurjectivePresentation f a b h ∧ AlgebraicSpace.Smooth h :=
  sorry

end Smooth

end AlgebraicGeometry.AlgebraicSpace.CohStack.Hom
