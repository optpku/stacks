/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Support
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.RestrictToScheme
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Topology
public import ReasLib.AlgebraicGeometry.Scheme.Module.Support

/-!
# Support of an étale pullback of a quasi-coherent module

For a quasi-coherent module on an algebraic space, the Zariski support of its
pullback along an étale morphism from a scheme is the inverse image of its support.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- The Zariski support of the pullback of a quasi-coherent module along an étale morphism
from a scheme is the inverse image of its support on the algebraic space. -/
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
