/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.Defs.Basic
public import stacks_project.Chap108.Lemma_108_4_2_LocallyOfFinitePresentation
public import stacks_project.Chap109.Lemma_109_17_1_Points
public import stacks_project.Chap109.Lemma_109_25_1_Separated

/-!
# Proper morphisms of CohStack-sized groupoid fibrations

A 1-morphism in `FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)`
is proper when it is separated, of finite type, and universally closed, matching
Definition 101.37.1 at the Hom-universe of `CohStack.toGroupoids`. Finite type
means quasi-compact and locally of finite type; locally of finite type is tested
on a smooth surjective algebraic-space presentation square; quasi-compactness is
tested on quasi-compact scheme slices; universal closedness is closedness of
`Points.map` of every 2-fibre-product projection.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.GroupScheme
open FiberedCategoryOver
open AlgebraicGeometry.AlgebraicSpace.CohStack (AlgebraicStack Points)
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

/-- The identity 1-morphism of a category fibred in groupoids is locally of
finite type. -/
instance id {S : Scheme.{u}}
    {X : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)} :
    LocallyOfFiniteType (𝟙 X) :=
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

/-- A 1-morphism `f : X ⟶ Y` of algebraic stacks over `S`, in the Hom-universe
of `CohStack.toGroupoids`, is quasi-compact if every 2-fibre product against a
morphism from a quasi-compact scheme admits a smooth surjective atlas from a
quasi-compact scheme. -/
@[mk_iff]
class QuasiCompact {S : Scheme.{u}}
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) : Prop where
  /-- The 2-fibre product of `f` with a morphism from a quasi-compact scheme
  admits a smooth surjective scheme atlas from a quasi-compact scheme. -/
  pullback_quasiCompact {U : Over S} (y : Classifying.slice U ⟶ Y)
      [CompactSpace U.left] :
    ∃ (W : Over S)
      (p : Classifying.slice W ⟶
        CategoryTheory.TwoFibreProduct.apex.{u + 1, u, u + 1, u + 1} f y),
      Classifying.Smooth p ∧ Classifying.Surjective p ∧ CompactSpace W.left

namespace QuasiCompact

/-- The identity 1-morphism of an algebraic stack is quasi-compact. -/
instance id {S : Scheme.{u}}
    {X : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    [AlgebraicStack X] : QuasiCompact (𝟙 X) :=
  sorry

/-- A quasi-compact 1-morphism pulls quasi-compact scheme slices back to stacks
that admit a quasi-compact smooth surjective scheme atlas. -/
theorem spec {S : Scheme.{u}}
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y} [QuasiCompact f]
    {U : Over S} (y : Classifying.slice U ⟶ Y) [CompactSpace U.left] :
    ∃ (W : Over S)
      (p : Classifying.slice W ⟶
        CategoryTheory.TwoFibreProduct.apex.{u + 1, u, u + 1, u + 1} f y),
      Classifying.Smooth p ∧ Classifying.Surjective p ∧ CompactSpace W.left :=
  sorry

end QuasiCompact

/-- A 1-morphism of algebraic stacks over `S`, in the Hom-universe of
`CohStack.toGroupoids`, is of finite type if it is quasi-compact and locally of
finite type. -/
@[mk_iff]
class FiniteType {S : Scheme.{u}}
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) : Prop
    extends QuasiCompact f, LocallyOfFiniteType f

namespace FiniteType

/-- A finite-type 1-morphism of algebraic stacks is quasi-compact and locally of
finite type. -/
theorem spec {S : Scheme.{u}}
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [FiniteType f] :
    QuasiCompact f ∧ LocallyOfFiniteType f :=
  sorry

/-- The identity 1-morphism of an algebraic stack is of finite type. -/
instance id {S : Scheme.{u}}
    {X : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    [AlgebraicStack X] : FiniteType (𝟙 X) :=
  sorry

/-- A quasi-compact 1-morphism that is locally of finite type is of finite
type. -/
instance instOfQuasiCompactLocallyOfFiniteType {S : Scheme.{u}}
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [QuasiCompact f] [LocallyOfFiniteType f] : FiniteType f :=
  sorry

end FiniteType

/-- A 1-morphism `f : X ⟶ Y` of algebraic stacks over `S`, in the Hom-universe
of `CohStack.toGroupoids`, is universally closed if every 2-fibre-product base
change induces a closed map on underlying point spaces. -/
@[mk_iff]
class UniversallyClosed {S : Scheme.{u}}
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) : Prop where
  /-- The second projection of every 2-fibre product of `f` is a closed map on
  points. -/
  closed_snd {Z : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
      [AlgebraicStack Z] (g : Z ⟶ Y)
      [AlgebraicStack
        (CategoryTheory.TwoFibreProduct.apex.{u + 1, u, u + 1, u + 1} f g)] :
    IsClosedMap
      (Points.map
        (CategoryTheory.TwoFibreProduct.snd.{u + 1, u, u + 1, u + 1} f g))

namespace UniversallyClosed

/-- The identity 1-morphism of an algebraic stack is universally closed. -/
instance id {S : Scheme.{u}}
    {X : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    [AlgebraicStack X] : UniversallyClosed (𝟙 X) :=
  sorry

/-- A universally closed 1-morphism has closed 2-fibre-product projections on
points. -/
theorem spec {S : Scheme.{u}}
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y} [UniversallyClosed f]
    {Z : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    [AlgebraicStack Z] (g : Z ⟶ Y)
    [AlgebraicStack
      (CategoryTheory.TwoFibreProduct.apex.{u + 1, u, u + 1, u + 1} f g)] :
    IsClosedMap
      (Points.map
        (CategoryTheory.TwoFibreProduct.snd.{u + 1, u, u + 1, u + 1} f g)) :=
  sorry

end UniversallyClosed

/-- A 1-morphism of algebraic stacks over `S`, in the Hom-universe of
`CohStack.toGroupoids`, is proper if it is separated, of finite type, and
universally closed. -/
@[mk_iff]
class Proper {S : Scheme.{u}}
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) : Prop
    extends Separated f, FiniteType f, UniversallyClosed f

namespace Proper

/-- A proper 1-morphism of algebraic stacks is separated, of finite type, and
universally closed. -/
theorem spec {S : Scheme.{u}}
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Proper f] :
    Separated f ∧ FiniteType f ∧ UniversallyClosed f :=
  sorry

/-- The identity 1-morphism of an algebraic stack is proper. -/
instance id {S : Scheme.{u}}
    {X : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    [AlgebraicStack X] : Proper (𝟙 X) :=
  sorry

/-- A separated, finite type, and universally closed 1-morphism of algebraic
stacks is proper. -/
instance instOfSeparatedFiniteTypeUniversallyClosed {S : Scheme.{u}}
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [Separated f] [FiniteType f] [UniversallyClosed f] : Proper f :=
  sorry

end Proper

end AlgebraicGeometry.AlgebraicSpace.CohStack.Hom
