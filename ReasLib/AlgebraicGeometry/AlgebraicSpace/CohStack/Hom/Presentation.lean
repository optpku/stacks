/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Representable

/-!
# Smooth surjective presentation squares
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.GroupScheme
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.CohStack.Hom

/-- A commutative square presenting a 1-morphism of categories fibred in
groupoids over `Over S` by algebraic spaces, with smooth vertical arrows,
surjective source atlas, and a 2-isomorphic comparison of the two paths
`Classifying.toGroupoids U ⟶ Y`. -/
def IsSmoothSurjectivePresentation {S : Scheme.{u}}
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    {U V : AlgebraicSpace S} (f : X ⟶ Y)
    (a : Classifying.toGroupoids U ⟶ X) (b : Classifying.toGroupoids V ⟶ Y)
    (h : U ⟶ V) : Prop :=
  Classifying.Smooth a ∧ Classifying.Surjective a ∧ Classifying.Smooth b ∧
    Nonempty (a ≫ f ≅ Classifying.toGroupoids.map h ≫ b)

namespace IsSmoothSurjectivePresentation

/-- Unfolding of a smooth surjective algebraic-space presentation square. -/
theorem iff {S : Scheme.{u}}
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    {U V : AlgebraicSpace S} (f : X ⟶ Y)
    (a : Classifying.toGroupoids U ⟶ X) (b : Classifying.toGroupoids V ⟶ Y)
    (h : U ⟶ V) :
    IsSmoothSurjectivePresentation f a b h ↔
      Classifying.Smooth a ∧ Classifying.Surjective a ∧ Classifying.Smooth b ∧
        Nonempty (a ≫ f ≅ Classifying.toGroupoids.map h ≫ b) :=
  sorry

/-- A smooth surjective algebraic-space presentation square is determined by
smoothness of the vertical arrows, surjectivity of the source atlas, and a
2-isomorphism of the two paths to `Y`. -/
theorem of {S : Scheme.{u}}
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    {U V : AlgebraicSpace S} {f : X ⟶ Y}
    {a : Classifying.toGroupoids U ⟶ X} {b : Classifying.toGroupoids V ⟶ Y}
    {h : U ⟶ V} (ha : Classifying.Smooth a) (hasurj : Classifying.Surjective a)
    (hb : Classifying.Smooth b)
    (hw : Nonempty (a ≫ f ≅ Classifying.toGroupoids.map h ≫ b)) :
    IsSmoothSurjectivePresentation f a b h :=
  sorry

/-- A smooth surjective algebraic-space presentation square has smooth vertical
arrows, a surjective source atlas, and a 2-isomorphism of the two paths to
`Y`. -/
theorem spec {S : Scheme.{u}}
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    {U V : AlgebraicSpace S} {f : X ⟶ Y}
    {a : Classifying.toGroupoids U ⟶ X} {b : Classifying.toGroupoids V ⟶ Y}
    {h : U ⟶ V} (H : IsSmoothSurjectivePresentation f a b h) :
    Classifying.Smooth a ∧ Classifying.Surjective a ∧ Classifying.Smooth b ∧
      Nonempty (a ≫ f ≅ Classifying.toGroupoids.map h ≫ b) :=
  sorry

end IsSmoothSurjectivePresentation

end AlgebraicGeometry.AlgebraicSpace.CohStack.Hom
