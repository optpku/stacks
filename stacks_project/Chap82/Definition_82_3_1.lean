module

public import stacks_project.Chap82.Definition_82_3_1_CycleGroup
public import stacks_project.Chap82.Definition_82_2_5_DeltaDimension
public import stacks_project.Chap72.Definition_72_4_1_Integral
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

section

variable {S : Scheme.{u}} {B X : AlgebraicSpace S}
  [UniversallyCatenary B] [IsQuasiSeparated B]
variable (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
variable (δ : Points B → ℤ) [IsDimensionFunction δ] (k : ℤ)

/- Definition 82.3.1 (1): In Situation 82.2.1, for good `X / B`, a cycle on `X`
is a locally finite formal ℤ-linear combination of integral closed subspaces
`Z ⊂ X`, encoded as `Function.locallyFinsupp (Points X) ℤ` on generic points of
`|X|` (Topology, Definition 5.28.4). -/
@[stacks 0EDZ]
#check (Function.locallyFinsupp (Points X) ℤ)

/-- Definition 82.3.1 (2): In Situation 82.2.1, for good `X / B` and `k ∈ ℤ`, a
`k`-cycle on `X` is a cycle `α` such that `n_Z ≠ 0` implies `dim_δ(Z) = k` for
every integral closed subspace `Z ⊂ X`. -/
@[stacks 0EDZ]
theorem Hom.mem_cycleGroup_iff_closedSubspaceDeltaDimension
    (α : Function.locallyFinsupp (Points X) ℤ) :
    α ∈ f.cycleGroup δ k ↔
      ∀ (Z : ClosedSubspace X) (hZ : IsIntegral Z.X) (ξ : Points X),
        IsGenericPoint ξ Z.pointsSet → α ξ ≠ 0 →
          f.closedSubspaceDeltaDimension δ Z = (k : EInt) :=
  sorry

/- Definition 82.3.1 (3): In Situation 82.2.1, the abelian group of all
`k`-cycles on `X` is `Z_k(X) = f.cycleGroup δ k`. -/
@[stacks 0EDZ]
#check (f.cycleGroup δ k : AddSubgroup (Function.locallyFinsupp (Points X) ℤ))

end

end AlgebraicGeometry.AlgebraicSpace
