module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.FiniteTypeOnReduction
import StacksCheckRecall

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
open AlgebraicGeometry.IsLocallyCountablyIndexed

/- Lemma 88.12.7: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
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
@[stacks 0GC7] #check
  (AlgebraicGeometry.IsLocallyCountablyIndexed.locallyOfFiniteTypeOnReduction_tfae :
    ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
      [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
      [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
      {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))}
      [IsLocallyCountablyIndexed X] [IsLocallyCountablyIndexed Y]
      (f : X ⟶ Y) [Fact (ChosenBigSite.IsSizeClosed 𝒮)],
      List.TFAE
        [etaleAffineLocally (fun φ ↦ φ.IsFiniteTypeOnReduction) f,
          existsCoverOnTarget (fun φ ↦ φ.IsFiniteTypeOnReduction) f,
          existsCoverOnSource (fun φ ↦ φ.IsFiniteTypeOnReduction) f,
          locallyOfFiniteTypeOnReduction f])

variable {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
variable [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
variable [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
variable {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))}
variable [IsLocallyCountablyIndexed X] [IsLocallyCountablyIndexed Y]

#check (AlgebraicGeometry.IsLocallyCountablyIndexed.locallyOfFiniteTypeOnReduction :
  (X ⟶ Y) → Prop)

#check (AlgebraicGeometry.IsLocallyCountablyIndexed.locallyOfFiniteTypeOnReduction_iff :
  ∀ (f : X ⟶ Y) [Fact (ChosenBigSite.IsSizeClosed 𝒮)],
    locallyOfFiniteTypeOnReduction f ↔
      ∃ φ : reduction X ⟶ reduction Y,
        φ ≫ reductionι Y = reductionι X ≫ f ∧
          locallyOfFiniteTypeOnEtaleSquares φ)

#check
  (AlgebraicGeometry.IsLocallyCountablyIndexed.etaleAffineLocally_iff_locallyOfFiniteTypeOnReduction :
    ∀ (f : X ⟶ Y) [Fact (ChosenBigSite.IsSizeClosed 𝒮)],
      etaleAffineLocally (fun φ ↦ φ.IsFiniteTypeOnReduction) f ↔
        locallyOfFiniteTypeOnReduction f)

#check
  (AlgebraicGeometry.IsLocallyCountablyIndexed.existsCoverOnTarget_iff_locallyOfFiniteTypeOnReduction :
    ∀ (f : X ⟶ Y) [Fact (ChosenBigSite.IsSizeClosed 𝒮)],
      existsCoverOnTarget (fun φ ↦ φ.IsFiniteTypeOnReduction) f ↔
        locallyOfFiniteTypeOnReduction f)

#check
  (AlgebraicGeometry.IsLocallyCountablyIndexed.existsCoverOnSource_iff_locallyOfFiniteTypeOnReduction :
    ∀ (f : X ⟶ Y) [Fact (ChosenBigSite.IsSizeClosed 𝒮)],
      existsCoverOnSource (fun φ ↦ φ.IsFiniteTypeOnReduction) f ↔
        locallyOfFiniteTypeOnReduction f)
