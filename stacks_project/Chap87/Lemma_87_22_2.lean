/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.List.TFAE
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap87.Definition_87_5_1_Taut
public import stacks_project.Chap87.Lemma_87_21_3

/-!
# Taut charts and representability by algebraic spaces

Lemma 87.22.2 records that a morphism of locally countably indexed formal
algebraic spaces is representable by algebraic spaces if and only if its
étale affine charts, or some Definition 87.11.1 covering of the target or of
the source, correspond to taut maps of `WAdm^count`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ChosenBigFppfSite TopologicalRing

universe u v

namespace AlgebraicGeometry.IsLocallyCountablyIndexed

/-- The Situation 87.21.2 predicate on morphisms of `WAdm^count` packing
tautness of `φ : B →+* A`. -/
abbrev wAdmCountTaut {A B : Type u}
    [CommRing A] [TopologicalSpace A] [IsWeaklyAdmissibleRing A] [IsCountablyIndexed A]
    [CommRing B] [TopologicalSpace B] [IsWeaklyAdmissibleRing B] [IsCountablyIndexed B]
    (φ : B →+* A) : Prop :=
  φ.IsTaut

/-- Unfold `wAdmCountTaut φ` as tautness of the corresponding map of
`WAdm^count`. -/
theorem wAdmCountTaut_iff {A B : Type u}
    [CommRing A] [TopologicalSpace A] [IsWeaklyAdmissibleRing A] [IsCountablyIndexed A]
    [CommRing B] [TopologicalSpace B] [IsWeaklyAdmissibleRing B] [IsCountablyIndexed B]
    (φ : B →+* A) : wAdmCountTaut φ ↔ φ.IsTaut := sorry

variable {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
variable [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
variable [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
variable {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))}
variable [IsLocallyCountablyIndexed X] [IsLocallyCountablyIndexed Y]
variable (f : X ⟶ Y)

/-- Lemma 87.22.2: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
locally countably indexed formal algebraic spaces over `S`. The following are
equivalent: `etaleAffineLocally wAdmCountTaut f`, that every commutative
square of affine formal algebraic spaces over `f` with representable étale
vertical arrows has top arrow corresponding to a taut map `B →+* A` of
`WAdm^count`; `existsCoverOnTarget wAdmCountTaut f`, that some covering
`{Y_ j ⟶ Y}` as in Definition 87.11.1 has, for each `j`, a covering
`{X_ ji ⟶ Y_ j ×_Y X}` as in Definition 87.11.1 whose maps `X_ ji ⟶ Y_ j`
correspond to taut maps of `WAdm^count`; `existsCoverOnSource wAdmCountTaut f`,
that some covering `{X_ i ⟶ X}` as in Definition 87.11.1 factors as
`X_ i ⟶ Y_ i ⟶ Y` with each `Y_ i` an affine formal algebraic space, each
`Y_ i ⟶ Y` representable by algebraic spaces and étale, and each
`X_ i ⟶ Y_ i` corresponding to a taut map of `WAdm^count`; and
`representableByAlgebraicSpaces f`. -/
@[stacks 0ANK]
theorem isTaut_tfae :
    List.TFAE [etaleAffineLocally wAdmCountTaut f, existsCoverOnTarget wAdmCountTaut f,
      existsCoverOnSource wAdmCountTaut f, representableByAlgebraicSpaces f] := sorry

/-- Condition (1) of Lemma 87.22.2 is equivalent to condition (4): testing taut
charts on every étale affine-chart square is equivalent to representability
by algebraic spaces. -/
theorem etaleAffineLocally_isTaut_iff :
    etaleAffineLocally wAdmCountTaut f ↔ representableByAlgebraicSpaces f := sorry

/-- Condition (2) of Lemma 87.22.2 is equivalent to condition (4): the existence
of a Definition 87.11.1 covering of the target and then of each fibre product
by taut charts is equivalent to representability by algebraic spaces. -/
theorem existsCoverOnTarget_isTaut_iff :
    existsCoverOnTarget wAdmCountTaut f ↔ representableByAlgebraicSpaces f := sorry

/-- Condition (3) of Lemma 87.22.2 is equivalent to condition (4): the existence
of a Definition 87.11.1 covering of the source factoring through affine étale
taut charts of the target is equivalent to representability by algebraic
spaces. -/
theorem existsCoverOnSource_isTaut_iff :
    existsCoverOnSource wAdmCountTaut f ↔ representableByAlgebraicSpaces f := sorry

end AlgebraicGeometry.IsLocallyCountablyIndexed
