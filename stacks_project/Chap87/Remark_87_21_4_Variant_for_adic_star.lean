module

public import Mathlib.Data.List.TFAE
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap87.Remark_87_21_4_Variant_for_adic_star_AdicStarRing
public import stacks_project.Chap87.Remark_87_21_4_Variant_for_adic_star_Local
public import stacks_project.Chap87.Remark_87_21_4_Variant_for_adic_star_MorphismProperty
public import stacks_project.Chap87.Remark_87_21_4_Variant_for_adic_star_WAdm
import StacksCheckRecall

/-!
# Local tests of morphism properties of locally adic* formal algebraic spaces

Remark 87.21.4 records the `WAdm^{adic*}` variant of Situation 87.21.2 and
Lemma 87.21.3: a property of morphisms of adic rings with a finitely generated
ideal of definition is local when the three étale-completion and finite-product
axioms hold, and the same three tests remain equivalent for morphisms of
locally adic* formal algebraic spaces.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ChosenBigFppfSite TopologicalRing

universe u v

/- Remark 87.21.4 (Variant for adic-star) (1): a property of morphisms of
`WAdm^{adic*}` is local when axioms (1), (2), (3) of Situation 87.21.2 hold
for morphisms of `WAdm^{adic*}`. -/
@[stacks 0ANH] #check TopologicalRing.IsAdicStarRing.IsLocalMorphismProperty

namespace AlgebraicGeometry.IsLocallyAdicStar

variable {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
variable [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
variable [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
variable {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))}
variable [IsLocallyAdicStar X] [IsLocallyAdicStar Y]
variable (P : ∀ {A B : Type u}
    [CommRing A] [TopologicalSpace A] [IsAdicStarRing A]
    [CommRing B] [TopologicalSpace B] [IsAdicStarRing B],
    (B →+* A) → Prop)
variable (f : X ⟶ Y)

/-- Remark 87.21.4 (Variant for adic-star) (2): Let `S` be a scheme. Let
`f : X ⟶ Y` be a morphism of locally adic* formal algebraic spaces over `S`.
Let `P` be a local property of morphisms of `WAdm^{adic*}`. The following are
equivalent: `etaleAffineLocally P f`, that every étale affine-chart square
over `f` has top arrow corresponding to a morphism of `WAdm^{adic*}` with
property `P`; `existsCoverOnTarget P f`, that some covering `{Y_ j ⟶ Y}` as
in Definition 87.11.1 has, for each `j`, a covering `{X_ ji ⟶ Y_ j ×_Y X}`
as in Definition 87.11.1 whose maps `X_ ji ⟶ Y_ j` correspond to morphisms
of `WAdm^{adic*}` with property `P`; and `existsCoverOnSource P f`, that some
covering `{X_ i ⟶ X}` as in Definition 87.11.1 factors as `X_ i ⟶ Y_ i ⟶ Y`
with each `Y_ i` an affine formal algebraic space, each `Y_ i ⟶ Y`
representable by algebraic spaces and étale, and each `X_ i ⟶ Y_ i`
corresponding to a morphism of `WAdm^{adic*}` with property `P`. -/
@[stacks 0ANH]
theorem tfae (hP : IsAdicStarRing.IsLocalMorphismProperty P) :
    List.TFAE [etaleAffineLocally P f, existsCoverOnTarget P f,
      existsCoverOnSource P f] := sorry

/-- Condition (1) of the Lemma 87.21.3 variant is equivalent to condition (2):
testing `P` on every étale affine-chart square is equivalent to the existence
of a Definition 87.11.1 covering of the target and then of each fibre
product. -/
theorem etaleAffineLocally_iff_existsCoverOnTarget
    (hP : IsAdicStarRing.IsLocalMorphismProperty P) :
    etaleAffineLocally P f ↔ existsCoverOnTarget P f := sorry

/-- Condition (1) of the Lemma 87.21.3 variant is equivalent to condition (3):
testing `P` on every étale affine-chart square is equivalent to the existence
of a Definition 87.11.1 covering of the source factoring through affine étale
charts of the target. -/
theorem etaleAffineLocally_iff_existsCoverOnSource
    (hP : IsAdicStarRing.IsLocalMorphismProperty P) :
    etaleAffineLocally P f ↔ existsCoverOnSource P f := sorry

end AlgebraicGeometry.IsLocallyAdicStar
