module

public import Mathlib.Data.List.TFAE
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap87.Lemma_87_20_10_Types
public import stacks_project.Chap87.Lemma_87_21_3_WAdm
public import stacks_project.Chap87.Lemma_87_21_3_Local

/-!
# Local tests of morphism properties of locally countably indexed formal algebraic spaces

Lemma 87.21.3 records that a local property `P` of morphisms of `WAdm^count`
lifts to a morphism `f : X ⟶ Y` of locally countably indexed formal algebraic
spaces over a scheme `S` by three equivalent tests: every étale affine-chart
square, some Definition 87.11.1 covering of the target and then of each fibre
product, and some Definition 87.11.1 covering of the source factoring through
affine étale charts of the target.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ChosenBigFppfSite TopologicalRing

universe u v

namespace AlgebraicGeometry.IsLocallyCountablyIndexed

variable {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
variable [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
variable [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
variable {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))}
variable [IsLocallyCountablyIndexed X] [IsLocallyCountablyIndexed Y]
variable (P : ∀ {A B : Type u}
    [CommRing A] [TopologicalSpace A] [IsWeaklyAdmissibleRing A] [IsCountablyIndexed A]
    [CommRing B] [TopologicalSpace B] [IsWeaklyAdmissibleRing B] [IsCountablyIndexed B],
    (B →+* A) → Prop)
variable (f : X ⟶ Y)

/-- Lemma 87.21.3: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
locally countably indexed formal algebraic spaces over `S`. Let `P` be a local
property of morphisms of `WAdm^count`. The following are equivalent:
`etaleAffineLocally P f`, that every étale affine-chart square over `f` has
top arrow corresponding to a morphism of `WAdm^count` with property `P`;
`existsCoverOnTarget P f`, that some covering `{Y_ j ⟶ Y}` as in Definition
87.11.1 has, for each `j`, a covering `{X_ ji ⟶ Y_ j ×_Y X}` as in Definition
87.11.1 whose maps `X_ ji ⟶ Y_ j` correspond to morphisms of `WAdm^count`
with property `P`; and `existsCoverOnSource P f`, that some covering
`{X_ i ⟶ X}` as in Definition 87.11.1 factors as `X_ i ⟶ Y_ i ⟶ Y` with each
`Y_ i` an affine formal algebraic space, each `Y_ i ⟶ Y` representable by
algebraic spaces and étale, and each `X_ i ⟶ Y_ i` corresponding to a morphism
of `WAdm^count` with property `P`. -/
@[stacks 0ANG]
theorem tfae (hP : IsLocalMorphismProperty P) :
    List.TFAE [etaleAffineLocally P f, existsCoverOnTarget P f,
      existsCoverOnSource P f] := sorry

/-- Condition (1) of Lemma 87.21.3 is equivalent to condition (2): testing `P`
on every étale affine-chart square is equivalent to the existence of a
Definition 87.11.1 covering of the target and then of each fibre product. -/
theorem etaleAffineLocally_iff_existsCoverOnTarget
    (hP : IsLocalMorphismProperty P) :
    etaleAffineLocally P f ↔ existsCoverOnTarget P f := sorry

/-- Condition (1) of Lemma 87.21.3 is equivalent to condition (3): testing `P`
on every étale affine-chart square is equivalent to the existence of a
Definition 87.11.1 covering of the source factoring through affine étale
charts of the target. -/
theorem etaleAffineLocally_iff_existsCoverOnSource
    (hP : IsLocalMorphismProperty P) :
    etaleAffineLocally P f ↔ existsCoverOnSource P f := sorry

end AlgebraicGeometry.IsLocallyCountablyIndexed
