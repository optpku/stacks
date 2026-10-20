module

public import stacks_project.Chap82.Lemma_82_28_1_Chern

/-! Total Chern class of a constant-rank finite locally free module. -/
@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Hom
open scoped BigOperators

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.ConstantRankChern

variable {S : Scheme.{u}} {B X : AlgebraicSpace S}
  [UniversallyCatenary B] [IsQuasiSeparated B]
variable (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
variable (δ : Points B → ℤ) [IsDimensionFunction δ]
variable (E : X.Modules) (q : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank (q + 1) E]

/-- The total Chern class of a finite locally free `𝒪_X`-module of rank
`q + 1`, as the finite sum of its homogeneous identity classes in
`A^*(X)`. -/
def total : ChowCohomology.ring δ f :=
  ∑ i : Fin (q + 2),
    ChowCohomology.homogeneous δ f i.val
      (degree f δ E q i.val (Nat.lt_succ_iff.mp i.isLt))

/-- Unfolding of `total` as the sum of homogeneous embeddings of `degree`. -/
theorem total_def :
    total f δ E q =
      ∑ i : Fin (q + 2),
        ChowCohomology.homogeneous δ f i.val
          (degree f δ E q i.val (Nat.lt_succ_iff.mp i.isLt)) :=
  sorry

/-- The degree-`i` component of the total Chern class is the homogeneous
class `c_i(E)`. -/
theorem total_coeff (i : ℕ) (hi : i ≤ q + 1) :
    (total f δ E q) (i : ℤ) = degree f δ E q i hi :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.ConstantRankChern