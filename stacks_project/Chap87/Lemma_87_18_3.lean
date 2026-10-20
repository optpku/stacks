module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap87.Lemma_87_12_1_Reduction
public import stacks_project.Chap87.Lemma_87_18_3_Affine

/-!
# Lemma 87.18.3

A formal algebraic space is an affine formal algebraic space if and only if
its reduction is an affine algebraic space.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open AlgebraicGeometry.ChosenBigFppfSite
open AlgebraicGeometry.IsFormalAlgebraicSpace

noncomputable section

universe u v

namespace AlgebraicGeometry.IsFormalAlgebraicSpace

/-- Lemma 87.18.3: Let `S` be a scheme. Let `X` be a formal algebraic space
over `S`. Then `X` is an affine formal algebraic space if and only if its
reduction `X_red` (Lemma 87.12.1) is an affine algebraic space. -/
@[stacks 0DE8]
theorem isAffineFormalAlgebraicSpace_iff_isAffine_reduction
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsFormalAlgebraicSpace X] :
    IsAffineFormalAlgebraicSpace X ↔ ChosenBigFppfSite.IsAffine (reduction X) :=
  sorry

/-- The reduction of an affine formal algebraic space is an affine algebraic
space. -/
instance instIsAffine_reduction {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsAffineFormalAlgebraicSpace X] :
    ChosenBigFppfSite.IsAffine (IsFormalAlgebraicSpace.reduction X) :=
  sorry

/-- A formal algebraic space whose reduction is affine is an affine formal
algebraic space. -/
theorem of_isAffine_reduction {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsFormalAlgebraicSpace X]
    [ChosenBigFppfSite.IsAffine (reduction X)] :
    IsAffineFormalAlgebraicSpace X :=
  sorry

end AlgebraicGeometry.IsFormalAlgebraicSpace
