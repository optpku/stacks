/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CoherentFormalModule.Epi

open AlgebraicGeometry CategoryTheory Opposite
open AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 76.42.2: for a scheme `S`, a Noetherian algebraic space `X` over `S`,
and a quasi-coherent ideal sheaf `I ⊂ 𝒪_X`, a morphism of coherent formal
modules is an epimorphism if and only if its first-stage component is an
epimorphism. -/
@[stacks 08B3] #check
  (AlgebraicGeometry.AlgebraicSpace.coherentFormalModules_epi_iff_firstStage_epi :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsNoetherian X]
      {I : IdealSubobject X} [IsQuasiCoherent I]
      {F G : CoherentFormalModules X I} (φ : F ⟶ G),
      Epi φ ↔ Epi (φ.hom.app (Opposite.op 1)))
