module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Support
public import stacks_project.Chap66.Lemma_66_5_5_PointsTopology
public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap66.Lemma_66_29_2_Pullback
public import stacks_project.Chap66.Proposition_66_32_1_Comparison
public import stacks_project.Chap67.Lemma_67_15_1_ModuleSupport

/-!
# Support of an étale pullback of a quasi-coherent module

For a quasi-coherent `𝒪_X`-module on an algebraic space, the Zariski support of its
pullback along an étale morphism from a scheme equals the inverse image of the
étale-site support.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- Lemma 67.15.1: Let `S` be a scheme. Let `X` be an algebraic space over `S`. Let `F` be a
quasi-coherent `𝒪_X`-module. Let `U` be a scheme and let `φ : U ⟶ X` be an étale morphism.
Then `Scheme.Modules.moduleSupport ((restrictToScheme U).obj ((pullback φ).obj F)) =
Points.mapOfOver φ ⁻¹' moduleSupport F`, where the left-hand side is the support of
`φ* F` as a quasi-coherent module on the scheme `U`. -/
@[stacks 07TY]
theorem moduleSupport_etalePullback_eq_preimage {S : Scheme.{u}} {X : AlgebraicSpace S}
    {U : Over S} (F : X.Modules) [F.IsQuasicoherent] (φ : ofOver U ⟶ X) [Etale φ] :
    Scheme.Modules.moduleSupport ((restrictToScheme U).obj ((pullback φ).obj F)) =
      Points.mapOfOver φ ⁻¹' moduleSupport F :=
  sorry

/-- A usual point of `U` lies in the Zariski support of `φ* F` if and only if its image
under `mapOfOver φ` lies in the étale-site support of `F`. -/
theorem mem_moduleSupport_etalePullback_iff {S : Scheme.{u}} {X : AlgebraicSpace S}
    {U : Over S} (F : X.Modules) [F.IsQuasicoherent] (φ : ofOver U ⟶ X) [Etale φ]
    (u : U.left) :
    u ∈ Scheme.Modules.moduleSupport ((restrictToScheme U).obj ((pullback φ).obj F)) ↔
      Points.mapOfOver φ u ∈ moduleSupport F :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
