/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap87.Lemma_87_12_1_Affine
public import stacks_project.Chap87.Lemma_87_12_1_Reduced
public import stacks_project.Chap87.Lemma_87_12_1_Reduction

/-!
# Lemma 87.12.1

The reduction of a formal algebraic space is a reduced algebraic space, the
canonical morphism into the formal algebraic space is a representable
thickening, and morphisms from reduced algebraic spaces factor uniquely
through it.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open AlgebraicGeometry.ChosenBigFppfSite
open AlgebraicGeometry.IsFormalAlgebraicSpace

noncomputable section

universe u v

namespace AlgebraicGeometry.IsFormalAlgebraicSpace

/-- Lemma 87.12.1 (1): the reduction of a formal algebraic space is a reduced
algebraic space. -/
@[stacks 0AIN, instance]
instance instIsReduced_reduction {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsFormalAlgebraicSpace X] : ChosenBigFppfSite.IsReduced (reduction X) := sorry

/-- Lemma 87.12.1 (2): the reduction morphism is representable by algebraic
spaces and is a thickening. -/
@[stacks 0AIN]
theorem representableThickening_reductionι {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsFormalAlgebraicSpace X] :
    representableByAlgebraicSpaces (reductionι X) ∧
      (MorphismProperty.inverseImage (@IsThickening) (𝒮.bigToScheme S)).relative
        (𝒮.bigTopology S).sheafifiedRepresentableFunctor (reductionι X) :=
  sorry

/-- Lemma 87.12.1 (3): a morphism from a reduced algebraic space to a formal
algebraic space factors uniquely through the reduction. -/
@[stacks 0AIN]
theorem existsUnique_lift {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsFormalAlgebraicSpace X] {U : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [ChosenBigFppfSite.IsReduced U] (g : U ⟶ X) :
    ∃! h : U ⟶ reduction X, h ≫ reductionι X = g := sorry

end AlgebraicGeometry.IsFormalAlgebraicSpace
