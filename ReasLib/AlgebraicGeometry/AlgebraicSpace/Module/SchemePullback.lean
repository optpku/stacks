/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.InverseImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.SchemeComparison

/-!
# Étale chart pullback of modules on algebraic spaces

Pulling an `𝒪_X`-module back along a morphism from a scheme and restricting to that
scheme produces a module on the chart.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- The pullback of an `𝒪_X`-module along a morphism from a represented algebraic space,
restricted to the underlying scheme of the chart. -/
def pullbackToScheme {U : Over S} (a : ofOver U ⟶ X) (F : X.Modules) : U.left.Modules :=
  (restrictToScheme U).obj ((pullback a).obj F)

/-- `pullbackToScheme a F` is restriction to the chart of the algebraic-space pullback of `F`. -/
theorem pullbackToScheme_obj {U : Over S} (a : ofOver U ⟶ X) (F : X.Modules) :
    pullbackToScheme a F = (restrictToScheme U).obj ((pullback a).obj F) :=
  rfl

/-- Pullback of a quasi-coherent module to a scheme chart remains quasi-coherent. -/
instance pullbackToScheme.instIsQuasicoherent {U : Over S} (a : ofOver U ⟶ X)
    (F : X.Modules) [F.IsQuasicoherent] : (pullbackToScheme a F).IsQuasicoherent :=
  restrictToScheme_isQuasicoherent U ((pullback a).obj F)
    (pullback_quasiCoherentModuleProperty a (inferInstance : F.IsQuasicoherent))

end AlgebraicGeometry.AlgebraicSpace.Modules
