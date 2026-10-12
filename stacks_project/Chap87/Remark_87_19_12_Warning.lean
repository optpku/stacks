/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap87.Lemma_87_19_8
public import stacks_project.Chap87.Remark_87_19_12_Warning_AdicPowerSeries
public import stacks_project.Chap110.Lemma_110_75_3
import StacksCheckRecall

/-!
# Remark 87.19.12 (Warning)

Lemmas 87.19.8, 87.19.9, and 87.19.10 are sharp: a continuous map of weakly
admissible rings need not induce a representable `Spf` morphism, and a
representable morphism of affine formal algebraic spaces with McQuillan target
need not have McQuillan source.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AffineFormalAlgebraicSpace AlgebraicGeometry.AlgebraicSpace
open AdicPowerSeries

noncomputable section

universe u

namespace AlgebraicGeometry.AffineFormalAlgebraicSpace

/-- The algebra map `k → k[[t]]` is a morphism of affine schemes over `Spec k`. -/
theorem algebraMap_spec_over {k : Type u} [Field k] :
    Spec.map (CommRingCat.ofHom (algebraMap k (AdicPowerSeries k))) ≫
      𝟙 (Spec (.of k)) =
      Spec.map (CommRingCat.ofHom (algebraMap k (AdicPowerSeries k))) :=
  sorry

/-- Remark 87.19.12 (Warning) (1): if `A` and `B` are weakly admissible rings
and `φ : A →+* B` is a continuous map, then `Spf(φ)` is in general not
representable. The example is the algebra map from a discrete field `k` to
`k[[t]]` with the `t`-adic topology. -/
@[stacks 0AN7]
theorem not_representableByAlgebraicSpaces_spfMap_algebraMap
    {k : Type u} [Field k] [TopologicalSpace k] [DiscreteTopology k]
    [HasWeakSheafify (Scheme.fppfTopology.over (Spec (.of k))) (Type u)] :
    ¬ AlgebraicSpace.representableByAlgebraicSpaces
        ((sheafToPresheaf (Scheme.fppfTopology.over (Spec (.of k))) (Type u)).map
          (spfMap (algebraMap k (AdicPowerSeries k)) continuous_algebraMap
            algebraMap_spec_over)) :=
  sorry

end AlgebraicGeometry.AffineFormalAlgebraicSpace

/- Remark 87.19.12 (Warning) (2): if `f : Y ⟶ X` is a representable morphism of
affine formal algebraic spaces and `X` is McQuillan, then `Y` need not be
McQuillan. -/
@[stacks 0AN7] #check AlgebraicGeometry.exists_representable_isMcQuillan_source_not
