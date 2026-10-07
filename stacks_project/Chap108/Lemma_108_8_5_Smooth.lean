module

public import stacks_project.Chap67.Lemma_67_37_4_Smooth
public import stacks_project.Chap108.Lemma_108_4_2_LocallyOfFinitePresentation

/-!
# Smooth morphisms of CohStack-sized groupoid fibrations

A 1-morphism in `FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)`
is smooth when some smooth algebraic-space presentation square with surjective
source atlas has smooth top arrow, matching Definition 101.33.1 at the
Hom-universe of `CohStack.toGroupoids`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.GroupScheme
open FiberedCategoryOver
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.CohStack.Hom

/-- A 1-morphism `f : X ⟶ Y` of categories fibred in groupoids over `Over S`, in
the Hom-universe of `CohStack.toGroupoids`, is smooth if some commutative square
with algebraic-space vertices, smooth vertical arrows, and surjective source
atlas has smooth top arrow. -/
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

/-- The identity 1-morphism of a category fibred in groupoids is smooth. -/
instance id {S : Scheme.{u}}
    {X : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)} :
    Smooth (𝟙 X) :=
  sorry

/-- A smooth morphism of algebraic spaces induces a smooth 1-morphism of
categories fibred in groupoids. -/
instance of_toGroupoids {S : Scheme.{u}} {U V : AlgebraicSpace S} (h : U ⟶ V)
    [AlgebraicSpace.Smooth h] :
    Smooth (Classifying.toGroupoids.map h) :=
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
