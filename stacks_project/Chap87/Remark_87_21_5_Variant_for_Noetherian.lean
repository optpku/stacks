module

public import Mathlib.Data.List.TFAE
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap87.Remark_87_21_5_Variant_for_Noetherian_Local
public import stacks_project.Chap87.Remark_87_21_5_Variant_for_Noetherian_MorphismProperty
import StacksCheckRecall

/-!
# Local tests of morphism properties of locally Noetherian formal algebraic spaces

Remark 87.21.5 records that a property `P` of morphisms of `WAdm^Noeth` is
local when the axioms of Situation 87.21.2 hold in that subcategory, and that
the same argument as Lemma 87.21.3 then yields three equivalent tests for a
morphism of locally Noetherian formal algebraic spaces over a scheme `S`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ChosenBigFppfSite TopologicalRing

universe u v

/- Remark 87.21.5 (Variant for Noetherian) (1): a property P of morphisms of
WAdm^Noeth is local when axioms (1), (2), (3) of Situation 87.21.2 hold for
morphisms of WAdm^Noeth. -/
@[stacks 0ANI] #check TopologicalRing.Noetherian.IsLocalMorphismProperty

namespace AlgebraicGeometry.IsFormalAlgebraicSpace.IsLocallyNoetherian

variable {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
variable [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
variable [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
variable {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))}
variable [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
variable (P : ∀ {A B : Type u}
    [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
    [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B],
    (B →+* A) → Prop)
variable (f : X ⟶ Y)

/-- Remark 87.21.5 (Variant for Noetherian) (2): Let `S` be a scheme. Let
`f : X ⟶ Y` be a morphism of locally Noetherian formal algebraic spaces over
`S`. Let `P` be a local property of morphisms of `WAdm^Noeth`. The following
are equivalent: `etaleAffineLocally P f`, that every étale affine-chart square
over `f` has top arrow corresponding to a morphism of `WAdm^Noeth` with
property `P`; `existsCoverOnTarget P f`, that some covering `{Y_ j ⟶ Y}` as in
Definition 87.11.1 has, for each `j`, a covering `{X_ ji ⟶ Y_ j ×_Y X}` as in
Definition 87.11.1 whose maps `X_ ji ⟶ Y_ j` correspond to morphisms of
`WAdm^Noeth` with property `P`; and `existsCoverOnSource P f`, that some
covering `{X_ i ⟶ X}` as in Definition 87.11.1 factors as `X_ i ⟶ Y_ i ⟶ Y`
with each `Y_ i` an affine formal algebraic space, each `Y_ i ⟶ Y`
representable by algebraic spaces and étale, and each `X_ i ⟶ Y_ i`
corresponding to a morphism of `WAdm^Noeth` with property `P`. -/
@[stacks 0ANI]
theorem tfae (hP : Noetherian.IsLocalMorphismProperty P) :
    List.TFAE [etaleAffineLocally P f, existsCoverOnTarget P f,
      existsCoverOnSource P f] := sorry

/-- Condition (1) of the Noetherian variant of Lemma 87.21.3 is equivalent to
condition (2): testing `P` on every étale affine-chart square is equivalent to
the existence of a Definition 87.11.1 covering of the target and then of each
fibre product. -/
theorem etaleAffineLocally_iff_existsCoverOnTarget
    (hP : Noetherian.IsLocalMorphismProperty P) :
    etaleAffineLocally P f ↔ existsCoverOnTarget P f := sorry

/-- Condition (1) of the Noetherian variant of Lemma 87.21.3 is equivalent to
condition (3): testing `P` on every étale affine-chart square is equivalent to
the existence of a Definition 87.11.1 covering of the source factoring through
affine étale charts of the target. -/
theorem etaleAffineLocally_iff_existsCoverOnSource
    (hP : Noetherian.IsLocalMorphismProperty P) :
    etaleAffineLocally P f ↔ existsCoverOnSource P f := sorry

end AlgebraicGeometry.IsFormalAlgebraicSpace.IsLocallyNoetherian
