/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.List.TFAE
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap87.Lemma_87_20_10
public import stacks_project.Chap87.Lemma_87_21_3
public import stacks_project.Chap88.Lemma_88_12_1_FiniteTypeReduction

/-!
# Finite type on reductions of locally countably indexed formal algebraic spaces

Lemma 88.12.7 records that a morphism of locally countably indexed formal
algebraic spaces is finite type on reduction in the sense of Lemma 88.12.1
on étale affine charts if and only if the induced map of reductions is
locally of finite type as a morphism of algebraic spaces.
-/

@[expose] public section

universe u v

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ChosenBigFppfSite IsFormalAlgebraicSpace TopologicalRing RingHom

namespace AlgebraicGeometry.IsLocallyCountablyIndexed

variable {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
variable [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
variable [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
variable {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))}
variable [IsLocallyCountablyIndexed X] [IsLocallyCountablyIndexed Y]

/-- The morphism `f : X ⟶ Y` of locally countably indexed formal algebraic
spaces has reduction locally of finite type when every sheaf map
`φ : reduction X ⟶ reduction Y` satisfying
`φ ≫ reductionι Y = reductionι X ≫ f` is locally of finite type on étale
squares. -/
def locallyOfFiniteTypeOnReduction (f : X ⟶ Y) : Prop :=
  ∀ φ : reduction X ⟶ reduction Y,
    φ ≫ reductionι Y = reductionι X ≫ f → locallyOfFiniteTypeOnEtaleSquares φ

/-- Finite type on reduction of `f` is equivalent to existence of a map of
reductions over `f` that is locally of finite type on étale squares. -/
theorem locallyOfFiniteTypeOnReduction_iff (f : X ⟶ Y) :
    locallyOfFiniteTypeOnReduction f ↔
      ∃ φ : reduction X ⟶ reduction Y,
        φ ≫ reductionι Y = reductionι X ≫ f ∧
          locallyOfFiniteTypeOnEtaleSquares φ :=
  sorry

/-- Lemma 88.12.7: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
locally countably indexed formal algebraic spaces over `S`. The following are
equivalent: `etaleAffineLocally (fun φ ↦ φ.IsFiniteTypeOnReduction) f`, that
every étale affine-chart square over `f` has top arrow corresponding to a
morphism of `WAdm^count` that is finite type on reduction; `existsCoverOnTarget
(fun φ ↦ φ.IsFiniteTypeOnReduction) f`, that some covering `{Y_ j ⟶ Y}` as in
Definition 87.11.1 has, for each `j`, a covering `{X_ ji ⟶ Y_ j ×_Y X}` as in
Definition 87.11.1 whose maps `X_ ji ⟶ Y_ j` correspond to morphisms of
`WAdm^count` that are finite type on reduction; `existsCoverOnSource
(fun φ ↦ φ.IsFiniteTypeOnReduction) f`, that some covering `{X_ i ⟶ X}` as in
Definition 87.11.1 factors as `X_ i ⟶ Y_ i ⟶ Y` with each `Y_ i` an affine
formal algebraic space, each `Y_ i ⟶ Y` representable by algebraic spaces and
étale, and each `X_ i ⟶ Y_ i` corresponding to a morphism of `WAdm^count` that
is finite type on reduction; and `locallyOfFiniteTypeOnReduction f`, that the
induced map of reductions `f_red : X_red ⟶ Y_red` is locally of finite type. -/
@[stacks 0GC7]
theorem locallyOfFiniteTypeOnReduction_tfae (f : X ⟶ Y) :
    List.TFAE
      [etaleAffineLocally (fun φ ↦ φ.IsFiniteTypeOnReduction) f,
        existsCoverOnTarget (fun φ ↦ φ.IsFiniteTypeOnReduction) f,
        existsCoverOnSource (fun φ ↦ φ.IsFiniteTypeOnReduction) f,
        locallyOfFiniteTypeOnReduction f] :=
  sorry

/-- Condition (1) of Lemma 88.12.7 is equivalent to condition (4): testing
finite type on reduction on every étale affine-chart square is equivalent to
the induced map of reductions being locally of finite type. -/
theorem etaleAffineLocally_iff_locallyOfFiniteTypeOnReduction (f : X ⟶ Y) :
    etaleAffineLocally (fun φ ↦ φ.IsFiniteTypeOnReduction) f ↔
      locallyOfFiniteTypeOnReduction f :=
  sorry

/-- Condition (2) of Lemma 88.12.7 is equivalent to condition (4): a
Definition 87.11.1 covering of the target and then of each fibre product
witnesses finite type on reduction iff the induced map of reductions is
locally of finite type. -/
theorem existsCoverOnTarget_iff_locallyOfFiniteTypeOnReduction (f : X ⟶ Y) :
    existsCoverOnTarget (fun φ ↦ φ.IsFiniteTypeOnReduction) f ↔
      locallyOfFiniteTypeOnReduction f :=
  sorry

/-- Condition (3) of Lemma 88.12.7 is equivalent to condition (4): a
Definition 87.11.1 covering of the source factoring through affine étale
charts of the target witnesses finite type on reduction iff the induced map
of reductions is locally of finite type. -/
theorem existsCoverOnSource_iff_locallyOfFiniteTypeOnReduction (f : X ⟶ Y) :
    existsCoverOnSource (fun φ ↦ φ.IsFiniteTypeOnReduction) f ↔
      locallyOfFiniteTypeOnReduction f :=
  sorry

end AlgebraicGeometry.IsLocallyCountablyIndexed
