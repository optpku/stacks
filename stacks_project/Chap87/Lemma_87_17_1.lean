/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.List.TFAE
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap87.Lemma_87_12_1_Reduction
public import stacks_project.Chap87.Lemma_87_17_1_Atlas
public import stacks_project.Chap87.Lemma_87_17_1_QuasiCompact

/-!
# Lemma 87.17.1

Characterizations of quasi-compactness of the reduction of a formal algebraic
space: a finite étale affine atlas, or a single affine étale cover.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open AlgebraicGeometry.ChosenBigFppfSite
open AlgebraicGeometry.IsFormalAlgebraicSpace

noncomputable section

universe u v

namespace AlgebraicGeometry.IsFormalAlgebraicSpace

/-- Lemma 87.17.1: Let `S` be a scheme. Let `X` be a formal algebraic space
over `S`. The following are equivalent: the reduction of `X` (Lemma 87.12.1)
is a quasi-compact algebraic space; there is an étale affine atlas
`{X_ i ⟶ X}` as in Definition 87.11.1 with finite index; and there is a
morphism `Y ⟶ X` representable by algebraic spaces which is étale and
surjective with `Y` an affine formal algebraic space. -/
@[stacks 0AJ9]
theorem tfae_quasiCompact {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsFormalAlgebraicSpace X] :
    List.TFAE [ChosenBigFppfSite.IsQuasiCompact (reduction X),
      HasFiniteAffineEtaleAtlas X, HasAffineEtaleCover X] := sorry

/-- The reduction of a formal algebraic space is a quasi-compact algebraic
space if and only if `X` admits a Definition 87.11.1 étale affine atlas with
finite index. -/
theorem isQuasiCompact_reduction_iff_hasFiniteAffineEtaleAtlas
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsFormalAlgebraicSpace X] :
    ChosenBigFppfSite.IsQuasiCompact (reduction X) ↔
      HasFiniteAffineEtaleAtlas X := sorry

/-- A formal algebraic space admits a finite étale affine atlas if and only if
it admits a single representable étale surjection from an affine formal
algebraic space. -/
theorem hasFiniteAffineEtaleAtlas_iff_hasAffineEtaleCover
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsFormalAlgebraicSpace X] :
    HasFiniteAffineEtaleAtlas X ↔ HasAffineEtaleCover X := sorry

/-- The reduction of a formal algebraic space is a quasi-compact algebraic
space if and only if there is a representable étale surjection from an affine
formal algebraic space. -/
theorem isQuasiCompact_reduction_iff_hasAffineEtaleCover
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsFormalAlgebraicSpace X] :
    ChosenBigFppfSite.IsQuasiCompact (reduction X) ↔
      HasAffineEtaleCover X := sorry

end AlgebraicGeometry.IsFormalAlgebraicSpace
