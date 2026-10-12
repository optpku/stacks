/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.List.TFAE
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap87.Lemma_87_12_1_Reduction
public import stacks_project.Chap87.Lemma_87_16_2_Pullback
public import stacks_project.Chap87.Lemma_87_16_2_Separated

/-!
# Lemma 87.16.2

Characterizations of separatedness of the reduction of a formal algebraic
space: affine fibre products of maps from affine schemes, with surjective
`ℤ`-tensor map on global sections.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open AlgebraicGeometry.ChosenBigFppfSite
open AlgebraicGeometry.IsFormalAlgebraicSpace

noncomputable section

universe u v

namespace AlgebraicGeometry.IsFormalAlgebraicSpace

/-- Lemma 87.16.2: Let `S` be a scheme. Let `X` be a formal algebraic space
over `S`. The following are equivalent: the reduction of `X` (Lemma 87.12.1)
is a separated algebraic space; and for morphisms `U ⟶ X`, `V ⟶ X` with
`U`, `V` affine, the fibre product `U ×_X V` is affine and
`Γ(U, ⊤) ⊗[ℤ] Γ(V, ⊤) ⟶ Γ(U ×_X V, ⊤)` is surjective, via `sectionTensor`. -/
@[stacks 0AJ6]
theorem tfae_separated {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsFormalAlgebraicSpace X] :
    List.TFAE [ChosenBigFppfSite.IsSeparated (reduction X),
      forallAffinePullbackAffineSurjective X] :=
  sorry

/-- The reduction of a formal algebraic space is a separated algebraic space
if and only if fibre products of morphisms from affine schemes to `X` are
affine with surjective `sectionTensor`. -/
theorem isSeparated_reduction_iff_forallAffinePullbackAffineSurjective
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsFormalAlgebraicSpace X] :
    ChosenBigFppfSite.IsSeparated (reduction X) ↔
      forallAffinePullbackAffineSurjective X :=
  sorry

end AlgebraicGeometry.IsFormalAlgebraicSpace
