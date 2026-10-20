/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.AssociatedPoints.Relative
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

/- Lemma 38.26.2: if a finite-type quasicoherent module over a locally finite-type
morphism to a local scheme is flat along the closed fiber, and every point of its relative
assassin specializes to that fiber, then it is flat over the base. -/
@[stacks 05UB]
#check
  (AlgebraicGeometry.Scheme.Modules.relativeAssassin.flatOver_of_specializesTo_closedFiber :
    ∀ {X S : Scheme.{u}} [IsAffine S] [IsLocalRing Γ(S, ⊤)]
        (f : X ⟶ S) [LocallyOfFiniteType f]
        (ℱ : X.Modules) [ℱ.IsQuasicoherent] [ℱ.IsFiniteType] (s : S)
        (hs : S.isoSpec.hom s = IsLocalRing.closedPoint Γ(S, ⊤))
        (h_ass : ∀ x ∈ AlgebraicGeometry.Scheme.Modules.relativeAssassin f ℱ,
          ∃ z : f.fiber s, x ⤳ f.fiberι s z)
        (h_flat : ∀ z : f.fiber s,
          AlgebraicGeometry.Scheme.Modules.flatOverAt ℱ f (f.fiberι s z)),
      AlgebraicGeometry.Scheme.Modules.flatOver ℱ f)

end AlgebraicGeometry
