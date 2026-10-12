/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Sites.Limits
public import stacks_project.Chap87.Definition_87_11_1_Formal
public import stacks_project.Chap87.Lemma_87_12_1_Affine

/-!
# Reduction of a formal algebraic space

The reduction of a formal algebraic space is the sheaf coequalizer of the
kernel pair of the coproduct of the reductions of an étale affine atlas.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open AlgebraicGeometry.ChosenBigFppfSite

noncomputable section

universe u v

namespace AlgebraicGeometry.IsFormalAlgebraicSpace

/-- The chosen index type of an étale affine atlas of a formal algebraic
space. -/
def atlasIndex {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsFormalAlgebraicSpace X] : Type (max u v) :=
  Classical.choose ‹IsFormalAlgebraicSpace X›.exists_atlas

/-- The chosen affine charts of an étale atlas of a formal algebraic space. -/
def atlasObj {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsFormalAlgebraicSpace X] :
    atlasIndex X → Sheaf (𝒮.bigTopology S) (Type (max u v)) :=
  Classical.choose (Classical.choose_spec ‹IsFormalAlgebraicSpace X›.exists_atlas)

/-- The chosen atlas maps from the affine charts into `X`. -/
def atlasπ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsFormalAlgebraicSpace X] : ∀ i, atlasObj X i ⟶ X :=
  Classical.choose
    (Classical.choose_spec
      (Classical.choose_spec ‹IsFormalAlgebraicSpace X›.exists_atlas))

/-- The chosen cofan of the étale affine atlas of `X`. -/
def atlasCofan {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsFormalAlgebraicSpace X] : Cofan (atlasObj X) :=
  Classical.choose
    (Classical.choose_spec
      (Classical.choose_spec
        (Classical.choose_spec ‹IsFormalAlgebraicSpace X›.exists_atlas)))

/-- The chosen cofan of the étale affine atlas is a colimit. -/
def atlasCofanIsColimit {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsFormalAlgebraicSpace X] : IsColimit (atlasCofan X) :=
  Classical.choose
    (Classical.choose_spec
      (Classical.choose_spec
        (Classical.choose_spec
          (Classical.choose_spec ‹IsFormalAlgebraicSpace X›.exists_atlas))))

/-- The chosen étale affine atlas retains affinity of charts, étaleness of
the atlas maps, the cofan, its colimit, and joint local surjectivity. -/
theorem atlasPresentation_spec {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsFormalAlgebraicSpace X] :
    (∀ i, IsAffineFormalAlgebraicSpace (atlasObj X i)) ∧
      (∀ i, etale (atlasπ X i)) ∧
        Sheaf.IsLocallySurjective
          (Cofan.IsColimit.desc (atlasCofanIsColimit X) (atlasπ X)) :=
  Classical.choose_spec
    (Classical.choose_spec
      (Classical.choose_spec
        (Classical.choose_spec
          (Classical.choose_spec ‹IsFormalAlgebraicSpace X›.exists_atlas))))

/-- Each chosen atlas chart is an affine formal algebraic space. -/
instance instIsAffineFormalAlgebraicSpace_atlasObj
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsFormalAlgebraicSpace X] (i : atlasIndex X) :
    IsAffineFormalAlgebraicSpace (atlasObj X i) :=
  (atlasPresentation_spec X).1 i

/-- The coproduct of the affine reductions of an étale atlas of `X`. -/
def atlasReduction {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsFormalAlgebraicSpace X] :
    Sheaf (𝒮.bigTopology S) (Type (max u v)) :=
  ∐ fun i ↦ IsAffineFormalAlgebraicSpace.reduction (atlasObj X i)

/-- The induced map from the coproduct of atlas reductions into `X`. -/
def atlasReductionι {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsFormalAlgebraicSpace X] : atlasReduction X ⟶ X :=
  Sigma.desc fun i ↦
    IsAffineFormalAlgebraicSpace.reductionι (atlasObj X i) ≫ atlasπ X i

/-- `atlasReduction X` is the coproduct of the affine reductions of the chosen
étale atlas. -/
theorem atlasReduction_spec {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsFormalAlgebraicSpace X] :
    atlasReduction X =
      ∐ fun i ↦ IsAffineFormalAlgebraicSpace.reduction (atlasObj X i) := sorry

/-- `atlasReductionι X` is the coproduct desc of the affine reduction
inclusions followed by the atlas maps. -/
theorem atlasReductionι_spec {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsFormalAlgebraicSpace X] :
    atlasReductionι X =
      Sigma.desc fun i ↦
        IsAffineFormalAlgebraicSpace.reductionι (atlasObj X i) ≫
          atlasπ X i := sorry

/-- The reduction of a formal algebraic space, as the coequalizer of the kernel
pair of the coproduct of atlas reductions. -/
def reduction {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsFormalAlgebraicSpace X] :
    Sheaf (𝒮.bigTopology S) (Type (max u v)) :=
  coequalizer (pullback.fst (atlasReductionι X) (atlasReductionι X))
    (pullback.snd (atlasReductionι X) (atlasReductionι X))

/-- The canonical morphism from the reduction of a formal algebraic space. -/
def reductionι {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsFormalAlgebraicSpace X] : reduction X ⟶ X :=
  coequalizer.desc (atlasReductionι X) pullback.condition

/-- The reduction of `X` is the coequalizer of the kernel pair of
`atlasReductionι X`. -/
theorem reduction_spec {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsFormalAlgebraicSpace X] :
    reduction X =
      coequalizer (pullback.fst (atlasReductionι X) (atlasReductionι X))
        (pullback.snd (atlasReductionι X) (atlasReductionι X)) := sorry

/-- The reduction morphism is the coequalizer desc of `atlasReductionι X`. -/
theorem reductionι_spec {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsFormalAlgebraicSpace X] :
    reductionι X = coequalizer.desc (atlasReductionι X) pullback.condition := sorry

/-- The reduction inclusion is representable by algebraic spaces. -/
theorem representableByAlgebraicSpaces_reductionι
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsFormalAlgebraicSpace X] :
    representableByAlgebraicSpaces (reductionι X) := sorry

/-- The reduction inclusion is a relative thickening on `(Sch/S)_fppf`. -/
theorem relative_isThickening_reductionι {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsFormalAlgebraicSpace X] :
    (MorphismProperty.inverseImage (@IsThickening) (𝒮.bigToScheme S)).relative
      (𝒮.bigTopology S).sheafifiedRepresentableFunctor (reductionι X) := sorry

/-- A morphism of formal algebraic spaces induces a unique map of reductions
over it. -/
theorem existsUnique_mapReduction {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y] (f : X ⟶ Y) :
    ∃! φ : reduction X ⟶ reduction Y, φ ≫ reductionι Y = reductionι X ≫ f :=
  sorry

end AlgebraicGeometry.IsFormalAlgebraicSpace
