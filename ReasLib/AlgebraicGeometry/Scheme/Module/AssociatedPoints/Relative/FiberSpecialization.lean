/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints.Relative.FlatPointClosure

@[expose] public section

open CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.relativeAssassin

/-- A relatively associated point specializing into a fiber specializes to an associated point
of the restricted module on that fiber when the module is flat over the base along the fiber. -/
theorem exists_associatedPoint_fiber_of_specializes {X S : Scheme.{u}} (f : X ⟶ S)
    [Scheme.Hom.FiniteType f] (ℱ : X.Modules) [ℱ.IsQuasicoherent] [ℱ.IsFiniteType]
    (s s' : S) (x' : X) (hx' : x' ∈ relativeAssassin f ℱ) (hx'_image : f x' = s')
    (hspecializes : s' ⤳ s)
    (hflat : ∀ z : f.fiber s, flatOverAt ℱ f (f.fiberι s z))
    (hx'_fiber : ∃ z : f.fiber s, x' ⤳ f.fiberι s z) :
    ∃ x : f.fiber s, x' ⤳ f.fiberι s x ∧
      x ∈ ((Scheme.Modules.pullback (f.fiberι s)).obj ℱ).associatedPoints := sorry

end AlgebraicGeometry.Scheme.Modules.relativeAssassin
