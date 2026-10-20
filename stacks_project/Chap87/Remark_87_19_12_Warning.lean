/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalSpectrum.PowerSeries
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.NonMcQuillan
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

noncomputable section

universe u

/- Remark 87.19.12 (Warning) (1): if `A` and `B` are weakly admissible rings
and `φ : A →+* B` is a continuous map, then `Spf(φ)` is in general not
representable. The example is the algebra map from a discrete field `k` to
`k[[t]]` with the `t`-adic topology. -/
@[stacks 0AN7] #check
  (AlgebraicGeometry.AffineFormalAlgebraicSpace.not_representableByAlgebraicSpaces_spfMap_algebraMap :
    ∀ {k : Type u} [Field k] [TopologicalSpace k] [DiscreteTopology k]
      [HasWeakSheafify (Scheme.fppfTopology.over (Spec (.of k))) (Type u)],
    ¬ AlgebraicSpace.representableByAlgebraicSpaces
        ((sheafToPresheaf (Scheme.fppfTopology.over (Spec (.of k))) (Type u)).map
          (AlgebraicGeometry.AffineFormalAlgebraicSpace.spfMap
            (algebraMap k (AdicPowerSeries k)) continuous_of_discreteTopology
            (CategoryTheory.Category.comp_id
              (Spec.map (CommRingCat.ofHom (algebraMap k (AdicPowerSeries k))))))))

/- Remark 87.19.12 (Warning) (2): if `f : Y ⟶ X` is a representable morphism of
affine formal algebraic spaces and `X` is McQuillan, then `Y` need not be
McQuillan. -/
@[stacks 0AN7] #check
  (AlgebraicGeometry.exists_representable_isMcQuillan_source_not :
    ∃ (𝒮 : ChosenBigFppfSite.{u, u+1}) (S : 𝒮.carrier)
      (_ : HasWeakSheafify (𝒮.bigTopology S) (Type (u+1)))
      (_ : HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (u+1))))
      (X Y : Sheaf (𝒮.bigTopology S) (Type (u+1)))
      (_ : IsAffineFormalAlgebraicSpace X) (_ : IsMcQuillan Y) (f : X ⟶ Y),
      (𝒮.bigTopology S).sheafifiedRepresentableFunctor.relativelyRepresentable f ∧
        ¬ IsMcQuillan X)
