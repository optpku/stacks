/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Support.EtalePullback
import StacksCheckRecall

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

/- Lemma 67.15.1: Let `S` be a scheme. Let `X` be an algebraic space over `S`. Let `F` be a
quasi-coherent `𝒪_X`-module. Let `U` be a scheme and let `φ : U ⟶ X` be an étale morphism.
Then `Scheme.Modules.moduleSupport ((restrictToScheme U).obj ((pullback φ).obj F)) =
Points.mapOfOver φ ⁻¹' moduleSupport F`, where the left-hand side is the support of
`φ* F` as a quasi-coherent module on the scheme `U`. -/
@[stacks 07TY] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.moduleSupport_etalePullback_eq_preimage :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S}
    (F : X.Modules) [F.IsQuasicoherent] (φ : ofOver U ⟶ X) [Etale φ],
    Scheme.Modules.moduleSupport ((restrictToScheme U).obj ((pullback φ).obj F)) =
      Points.mapOfOver φ ⁻¹' moduleSupport F)

/- A usual point of `U` lies in the Zariski support of `φ* F` if and only if its image
under `mapOfOver φ` lies in the étale-site support of `F`. -/
#check (AlgebraicGeometry.AlgebraicSpace.Modules.mem_moduleSupport_etalePullback_iff :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S}
    (F : X.Modules) [F.IsQuasicoherent] (φ : ofOver U ⟶ X) [Etale φ] (u : U.left),
    u ∈ Scheme.Modules.moduleSupport ((restrictToScheme U).obj ((pullback φ).obj F)) ↔
      Points.mapOfOver φ u ∈ moduleSupport F)
