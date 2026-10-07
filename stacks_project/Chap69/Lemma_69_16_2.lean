module

public import stacks_project.Chap69.Lemma_69_16_2_ToSpec
public import stacks_project.Chap69.Lemma_69_16_2_Tensor
public import stacks_project.Chap69.Situation_69_16_1

/-!
# Lemma 69.16.2

In Situation 69.16.1, the absolute canonical morphism `p : X → Spec A` satisfies
`p_*(M ⊗_A 𝒪_X) ≅ tilde M` and `Γ(X, M ⊗_A 𝒪_X) ≅ M`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 69.16.2 (1): In Situation 69.16.1, the canonical map
`tildeOnSpec X M ⟶ (toSpecAPushforward X).obj (tensorOX X M)` on `Spec A`
is an isomorphism. This direct image includes the projection from `S × Spec A`. -/
@[stacks 07UZ]
instance pushforward_tensorOX {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsQuasiSeparated X]
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u})]
    [HasVanishingH1 X] (M : ModuleCat.{u} (globalSectionsRing X)) :
    IsIso (tensorOXPushforwardUnit X M) :=
  sorry

/-- Lemma 69.16.2 (2): In Situation 69.16.1, for an A-module M one has
Γ(X, tensorOX X M) ≅ M, as the canonical A-linear comparison
tensorOXSectionsUnit : M ⟶ moduleGlobalSections X (tensorOX X M). -/
@[stacks 07UZ]
instance tensorOX_globalSections {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsQuasiSeparated X]
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u})]
    [HasVanishingH1 X] (M : ModuleCat.{u} (globalSectionsRing X)) :
    IsIso (tensorOXSectionsUnit X M) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
