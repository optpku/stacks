/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.Specialization.Dimension
public import stacks_project.Chap65.Definition_65_13_2_Separation
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap68.Definition_68_25_4_UniversallyCatenary
public import stacks_project.Chap82.Lemma_82_10_2_Localization

/-!
# Exactness of the open-closed localization sequence of cycle groups

In the good setup of Situation 82.2.1, restriction to an open subspace and
pushforward from its reduced closed complement form an exact complex of
`k`-cycle groups, surjective onto the cycle group of the open subspace.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom
namespace Localization

/-- Lemma 82.10.2: In Situation 82.2.1 let `X / B` be good. Let `U ⊂ X` be an
open subspace. Let `Y` be the reduced closed subspace of `X` with
`|Y| = |X| \ |U|` and denote `i : Y ⟶ X` the inclusion morphism. For every
`k ∈ ℤ` the sequence `Z_k(Y) ⟶ Z_k(X) ⟶ Z_k(U) ⟶ 0` given by `i_*` then
`j^*` is an exact complex of abelian groups. Here `Y` is `U.reducedComplement`,
`i` is `Y.ι`, `j` is `U.ι`, and `Z_k` is `cycleGroup` of the structure morphism
to `B`. -/
@[stacks 0EP9]
theorem exact {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (U : OpenSubspace X) (k : ℤ) :
    (complex f δ U k).Exact ∧ Epi (complex f δ U k).g :=
  sorry

end Localization
end AlgebraicGeometry.AlgebraicSpace.Hom
