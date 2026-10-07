module

public import Mathlib.Data.List.TFAE
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap87.Lemma_87_12_1_Reduction
public import stacks_project.Chap87.Lemma_87_16_1_Pullback
public import stacks_project.Chap87.Lemma_87_16_1_QuasiSeparated

/-!
# Lemma 87.16.1

Characterizations of quasi-separatedness of the reduction of a formal
algebraic space: quasi-compact fibre products of maps from quasi-compact
schemes, or equivalently from affine schemes.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open AlgebraicGeometry.ChosenBigFppfSite
open AlgebraicGeometry.IsFormalAlgebraicSpace

noncomputable section

universe u v

namespace AlgebraicGeometry.IsFormalAlgebraicSpace

/-- Lemma 87.16.1: Let `S` be a scheme. Let `X` be a formal algebraic space
over `S`. The following are equivalent: the reduction of `X` (Lemma 87.12.1)
is a quasi-separated algebraic space; for morphisms `U ⟶ X`, `V ⟶ X` with
`U`, `V` quasi-compact schemes the fibre product `U ×_X V` is quasi-compact;
and the same with `U`, `V` affine. -/
@[stacks 0AJ5]
theorem tfae_quasiSeparated {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsFormalAlgebraicSpace X] :
    List.TFAE [ChosenBigFppfSite.IsQuasiSeparated (reduction X),
      forallQuasiCompactPullback X, forallAffineQuasiCompactPullback X] :=
  sorry

/-- The reduction of a formal algebraic space is a quasi-separated algebraic
space if and only if fibre products of morphisms from quasi-compact schemes
to `X` are quasi-compact. -/
theorem isQuasiSeparated_reduction_iff_forallQuasiCompactPullback
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsFormalAlgebraicSpace X] :
    ChosenBigFppfSite.IsQuasiSeparated (reduction X) ↔
      forallQuasiCompactPullback X := sorry

/-- Fibre products of morphisms from quasi-compact schemes to a formal
algebraic space are quasi-compact if and only if the same holds for morphisms
from affine schemes. -/
theorem forallQuasiCompactPullback_iff_forallAffineQuasiCompactPullback
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsFormalAlgebraicSpace X] :
    forallQuasiCompactPullback X ↔ forallAffineQuasiCompactPullback X :=
  sorry

/-- The reduction of a formal algebraic space is a quasi-separated algebraic
space if and only if fibre products of morphisms from affine schemes to `X`
are quasi-compact. -/
theorem isQuasiSeparated_reduction_iff_forallAffineQuasiCompactPullback
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsFormalAlgebraicSpace X] :
    ChosenBigFppfSite.IsQuasiSeparated (reduction X) ↔
      forallAffineQuasiCompactPullback X := sorry

end AlgebraicGeometry.IsFormalAlgebraicSpace
