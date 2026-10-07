module

public import Mathlib.Data.List.TFAE
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap87.Definition_87_5_1_Taut
public import stacks_project.Chap87.Definition_87_29_1_TopologicallyOfFiniteType
public import stacks_project.Chap87.Lemma_87_21_3
public import stacks_project.Chap87.Lemma_87_20_10

/-!
# Taut topologically finite-type charts and local finite type

Lemma 87.29.9 records that a morphism of locally countably indexed formal
algebraic spaces is locally of finite type if and only if its étale affine
charts, or some Definition 87.11.1 covering of the target or of the source,
correspond to taut topologically finite-type maps of `WAdm^count`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ChosenBigFppfSite TopologicalRing

universe u v

namespace AlgebraicGeometry.IsLocallyCountablyIndexed

/-- The Situation 87.21.2 predicate on morphisms of `WAdm^count` packing
tautness and topological finite type of `φ : B →+* A`. -/
abbrev wAdmCountTautTopologicallyOfFiniteType {A B : Type u}
    [CommRing A] [TopologicalSpace A] [IsWeaklyAdmissibleRing A] [IsCountablyIndexed A]
    [CommRing B] [TopologicalSpace B] [IsWeaklyAdmissibleRing B] [IsCountablyIndexed B]
    (φ : B →+* A) : Prop :=
  φ.IsTaut ∧ φ.TopologicallyOfFiniteType

/-- Unfold `wAdmCountTautTopologicallyOfFiniteType φ` as tautness together with
topological finite type of the corresponding map of `WAdm^count`. -/
theorem wAdmCountTautTopologicallyOfFiniteType_iff {A B : Type u}
    [CommRing A] [TopologicalSpace A] [IsWeaklyAdmissibleRing A] [IsCountablyIndexed A]
    [CommRing B] [TopologicalSpace B] [IsWeaklyAdmissibleRing B] [IsCountablyIndexed B]
    (φ : B →+* A) :
    wAdmCountTautTopologicallyOfFiniteType φ ↔
      φ.IsTaut ∧ φ.TopologicallyOfFiniteType := sorry

variable {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
variable [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
variable [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]

/-- A morphism of sheaves on `(Sch/S)_fppf` is locally of finite type in the
sense of Definition 87.24.1 when it is representable by algebraic spaces and
every scheme pullback is locally of finite type as a morphism of algebraic
spaces. -/
@[mk_iff]
class LocallyOfFiniteType {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    (f : X ⟶ Y) : Prop where
  /-- `f` is representable by algebraic spaces. -/
  representable : representableByAlgebraicSpaces f
  /-- Every scheme pullback of `f` is locally of finite type in the
  algebraic-space sense. -/
  of_pullback :
    ∀ ⦃U : 𝒮.bigSite S⦄ (ξ : (𝒮.bigTopology S).sheafifiedRepresentable U ⟶ Y),
      locallyOfFiniteTypeOnEtaleSquares (pullback.fst ξ f)

namespace LocallyOfFiniteType

/-- The identity morphism of a sheaf on `(Sch/S)_fppf` is locally of finite
type. -/
instance id {X : Sheaf (𝒮.bigTopology S) (Type (max u v))} :
    LocallyOfFiniteType (𝟙 X) := sorry

/-- A morphism of sheaves is locally of finite type when it is representable by
algebraic spaces and every scheme pullback is locally of finite type as a
morphism of algebraic spaces. -/
theorem spec {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))} (f : X ⟶ Y)
    [LocallyOfFiniteType f] :
    representableByAlgebraicSpaces f ∧
      ∀ ⦃U : 𝒮.bigSite S⦄ (ξ : (𝒮.bigTopology S).sheafifiedRepresentable U ⟶ Y),
        locallyOfFiniteTypeOnEtaleSquares (pullback.fst ξ f) := sorry

end LocallyOfFiniteType

variable {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))}
variable [IsLocallyCountablyIndexed X] [IsLocallyCountablyIndexed Y]
variable (f : X ⟶ Y)

/-- Lemma 87.29.9: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
locally countably indexed formal algebraic spaces over `S`. The following are
equivalent: `etaleAffineLocally wAdmCountTautTopologicallyOfFiniteType f`,
that every commutative square of affine formal algebraic spaces over `f` with
representable étale vertical arrows has top arrow corresponding to a taut
topologically finite-type map `B →+* A` of `WAdm^count`;
`existsCoverOnTarget wAdmCountTautTopologicallyOfFiniteType f`, that some
covering `{Y_ j ⟶ Y}` as in Definition 87.11.1 has, for each `j`, a covering
`{X_ ji ⟶ Y_ j ×_Y X}` as in Definition 87.11.1 whose maps `X_ ji ⟶ Y_ j`
correspond to taut topologically finite-type maps of `WAdm^count`;
`existsCoverOnSource wAdmCountTautTopologicallyOfFiniteType f`, that some
covering `{X_ i ⟶ X}` as in Definition 87.11.1 factors as
`X_ i ⟶ Y_ i ⟶ Y` with each `Y_ i` an affine formal algebraic space, each
`Y_ i ⟶ Y` representable by algebraic spaces and étale, and each
`X_ i ⟶ Y_ i` corresponding to a taut topologically finite-type map of
`WAdm^count`; and `LocallyOfFiniteType f`. -/
@[stacks 0ANW]
theorem locallyOfFiniteType_tfae :
    List.TFAE
      [etaleAffineLocally wAdmCountTautTopologicallyOfFiniteType f,
        existsCoverOnTarget wAdmCountTautTopologicallyOfFiniteType f,
        existsCoverOnSource wAdmCountTautTopologicallyOfFiniteType f,
        LocallyOfFiniteType f] := sorry

/-- Condition (1) of Lemma 87.29.9 is equivalent to condition (4): testing taut
topologically finite-type charts on every étale affine-chart square is
equivalent to `f` being locally of finite type. -/
theorem etaleAffineLocally_iff_locallyOfFiniteType :
    etaleAffineLocally wAdmCountTautTopologicallyOfFiniteType f ↔
      LocallyOfFiniteType f := sorry

/-- Condition (2) of Lemma 87.29.9 is equivalent to condition (4): the existence
of a Definition 87.11.1 covering of the target and then of each fibre product
by taut topologically finite-type charts is equivalent to `f` being locally of
finite type. -/
theorem existsCoverOnTarget_iff_locallyOfFiniteType :
    existsCoverOnTarget wAdmCountTautTopologicallyOfFiniteType f ↔
      LocallyOfFiniteType f := sorry

/-- Condition (3) of Lemma 87.29.9 is equivalent to condition (4): the existence
of a Definition 87.11.1 covering of the source factoring through affine étale
taut topologically finite-type charts of the target is equivalent to `f` being
locally of finite type. -/
theorem existsCoverOnSource_iff_locallyOfFiniteType :
    existsCoverOnSource wAdmCountTautTopologicallyOfFiniteType f ↔
      LocallyOfFiniteType f := sorry

end AlgebraicGeometry.IsLocallyCountablyIndexed
