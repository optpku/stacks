/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints.Relative.FiberSpecialization
import StacksCheckRecall

@[expose] public section

open CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry
namespace Scheme.Modules.relativeAssassin

/- Lemma 38.18.1: a relatively associated point specializing into a fiber specializes to
an associated point of the restricted module on that fiber, provided the module is flat over
the base at every point of the fiber. -/
@[stacks 05L3] #check
  (AlgebraicGeometry.Scheme.Modules.relativeAssassin.exists_associatedPoint_fiber_of_specializes :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [Scheme.Hom.FiniteType f]
      (ℱ : X.Modules) [ℱ.IsQuasicoherent] [ℱ.IsFiniteType]
      (s s' : S) (x' : X) (hx' : x' ∈ relativeAssassin f ℱ) (hx'_image : f x' = s')
      (hspecializes : s' ⤳ s)
      (hflat : ∀ z : f.fiber s, flatOverAt ℱ f (f.fiberι s z))
      (hx'_fiber : ∃ z : f.fiber s, x' ⤳ f.fiberι s z),
      ∃ x : f.fiber s, x' ⤳ f.fiberι s x ∧
        x ∈ ((Scheme.Modules.pullback (f.fiberι s)).obj ℱ).associatedPoints)

end Scheme.Modules.relativeAssassin
end AlgebraicGeometry
