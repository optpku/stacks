/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Lemma_67_28_11_LocallyOfFinitePresentation
public import stacks_project.Chap110.Lemma_110_53_1

/-!
# Locally of finite presentation for CohStack-sized groupoid fibrations

A 1-morphism in `FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)`
is locally of finite presentation when some smooth algebraic-space presentation
square with surjective source atlas has locally-of-finite-presentation top
arrow, matching Definition 101.27.1 at the Hom-universe of
`CohStack.toGroupoids`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.GroupScheme
open FiberedCategoryOver
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

/-- A 1-morphism `f : X ⟶ Y` of categories fibred in groupoids over `Over S`, in
the Hom-universe of `CohStack.toGroupoids`, is locally of finite presentation if
some commutative square with algebraic-space vertices, smooth vertical arrows,
and surjective source atlas has locally-of-finite-presentation top arrow. -/
class LocallyOfFinitePresentation {S : Scheme.{u}}
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    (f : X ⟶ Y) : Prop where
  /-- There is a smooth presentation of `f` by algebraic spaces whose source
  atlas is surjective and whose top arrow is locally of finite presentation. -/
  exists_surjective_smooth_presentation :
    ∃ (U V : AlgebraicSpace S) (a : Classifying.toGroupoids U ⟶ X)
      (b : Classifying.toGroupoids V ⟶ Y) (h : U ⟶ V),
      IsSmoothSurjectivePresentation f a b h ∧
        AlgebraicSpace.LocallyOfFinitePresentation h

/-- A 1-morphism is locally of finite presentation if and only if it admits a
smooth algebraic-space presentation with surjective source atlas and
locally-of-finite-presentation top arrow. -/
theorem locallyOfFinitePresentation_iff {S : Scheme.{u}}
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    (f : X ⟶ Y) :
    LocallyOfFinitePresentation f ↔
      ∃ (U V : AlgebraicSpace S) (a : Classifying.toGroupoids U ⟶ X)
        (b : Classifying.toGroupoids V ⟶ Y) (h : U ⟶ V),
        IsSmoothSurjectivePresentation f a b h ∧
          AlgebraicSpace.LocallyOfFinitePresentation h :=
  sorry

namespace LocallyOfFinitePresentation

/-- A morphism of algebraic spaces that is locally of finite presentation
induces a 1-morphism of categories fibred in groupoids that is locally of
finite presentation. -/
instance of_toGroupoids {S : Scheme.{u}} {U V : AlgebraicSpace S} (h : U ⟶ V)
    [AlgebraicSpace.LocallyOfFinitePresentation h] :
    LocallyOfFinitePresentation (Classifying.toGroupoids.map h) :=
  sorry

/-- A locally-of-finite-presentation 1-morphism admits a smooth algebraic-space
presentation with surjective source atlas and locally-of-finite-presentation
top arrow. -/
theorem spec {S : Scheme.{u}}
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    (f : X ⟶ Y) [LocallyOfFinitePresentation f] :
    ∃ (U V : AlgebraicSpace S) (a : Classifying.toGroupoids U ⟶ X)
      (b : Classifying.toGroupoids V ⟶ Y) (h : U ⟶ V),
      IsSmoothSurjectivePresentation f a b h ∧
        AlgebraicSpace.LocallyOfFinitePresentation h :=
  sorry

end LocallyOfFinitePresentation

end AlgebraicGeometry.AlgebraicSpace.CohStack.Hom
