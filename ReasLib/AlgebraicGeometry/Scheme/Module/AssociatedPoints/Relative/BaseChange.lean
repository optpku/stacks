/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints.Relative
public import ReasLib.AlgebraicGeometry.Scheme.Module.Pullback.LocalGeneration
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.BaseChange

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.relativeAssassin

/-- In a cartesian square whose right-hand morphism is locally of finite type, a point is
relatively associated to the pullback of a quasicoherent module exactly when its image is
relatively associated and its corresponding point in the residue-field tensor spectrum is
generic. -/
theorem mem_pullback_iff
    {X S S' X' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S} {g' : X' ⟶ X}
    {f' : X' ⟶ S'} (sq : IsPullback g' f' f g) [LocallyOfFiniteType f]
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] (x' : X') :
    x' ∈ relativeAssassin f' ((Scheme.Modules.pullback g').obj ℱ) ↔
      g' x' ∈ relativeAssassin f ℱ ∧
        let z : (CategoryTheory.Limits.pullback f g : Scheme) := sq.isoPullback.hom x'
        Scheme.Pullback.SpecOfPoint z ∈
          genericPoints (Spec (Scheme.Pullback.Triplet.ofPoint z).tensor) := sorry

end AlgebraicGeometry.Scheme.Modules.relativeAssassin

namespace AlgebraicGeometry.Scheme.Hom

/-- Containment of the associated points of a finite-type quasicoherent module in an open
subset of a fiber is invariant under arbitrary base change. -/
theorem associatedPoints_fiber_subset_iff_of_isPullback
    {X S S' X' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) (g' : X' ⟶ X)
    (f' : X' ⟶ S') (sq : IsPullback g' f' f g) [LocallyOfFiniteType f]
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] [ℱ.IsFiniteType] (U : X.Opens)
    (s' : S') :
    ((Scheme.Modules.pullback (f.fiberι (g s'))).obj ℱ).associatedPoints ⊆
        (f.fiberι (g s')) ⁻¹' (U : Set X) ↔
      ((Scheme.Modules.pullback (f'.fiberι s')).obj
          ((Scheme.Modules.pullback g').obj ℱ)).associatedPoints ⊆
        (f'.fiberι s') ⁻¹' (g' ⁻¹' (U : Set X)) := sorry

end AlgebraicGeometry.Scheme.Hom
