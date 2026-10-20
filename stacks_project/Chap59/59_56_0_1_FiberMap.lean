/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Etale.StalkGaloisAction

open CategoryTheory Opposite
open AlgebraicGeometry

@[expose] public section

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Etale

/- The geometric-point automorphism's action on pointed étale neighborhoods. -/
#check (AlgebraicGeometry.Scheme.Etale.geometricPointFiberMap :
    ∀ {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω],
      (s : Spec (.of Ω) ⟶ S) → (σ : Over.mk s ≅ Over.mk s) →
      (Scheme.pointSmallEtale s).fiber ⟶ (Scheme.pointSmallEtale s).fiber)

end AlgebraicGeometry.Scheme.Etale
