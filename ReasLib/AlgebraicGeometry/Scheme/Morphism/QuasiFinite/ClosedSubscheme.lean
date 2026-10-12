/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Noetherian
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.ClosedPoint
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite
import ReasLib.RingTheory.QuasiFinite.LocalRing

/-!
# Closed subschemes quasi-finite at a point

This file records an existence result for closed subschemes that are quasi-finite at a
specified point while retaining a prescribed specialization away from its fibre.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A locally finite-type morphism to a locally Noetherian scheme admits a closed subscheme
through a fibre-closed point that is quasi-finite there and retains, in a prescribed open,
a specializing point whose image lies outside the fibre. -/
theorem exists_closedSubscheme_quasiFiniteAt_of_specializes
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    [IsLocallyNoetherian S] (x : X) (U : X.Opens)
    (hclosed : f.asFiber x ∈ closedPoints (f.fiber (f x)))
    (hspecializes : ∃ x' : X,
      x' ∈ U ∧ Specializes x' x ∧ f x' ≠ f x) :
    ∃ (Z : X.IdealSheafData) (hxZ : x ∈ Z.support),
      FiniteType.QuasiFiniteAt (Z.subschemeι ≫ f) ⟨x, hxZ⟩ ∧
        ∃ z : X, z ∈ Z.support ∧ z ∈ U ∧
          Specializes z x ∧ f z ≠ f x := sorry

/-- A locally finite-type morphism to a locally Noetherian scheme admits a closed subscheme
through a fibre-closed point that is quasi-finite there when the point lies in the closure
of an open set disjoint from its fibre. The subscheme retains a specializing point in that
open set whose image lies outside the fibre. -/
theorem exists_closedSubscheme_quasiFiniteAt_of_mem_closure
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    [IsLocallyNoetherian S] (x : X) (U : X.Opens)
    (hclosed : f.asFiber x ∈ closedPoints (f.fiber (f x)))
    (hdisjoint : Disjoint (U : Set X) (f ⁻¹' {f x}))
    (hxU : x ∈ closure (U : Set X)) :
    ∃ (Z : X.IdealSheafData) (hxZ : x ∈ Z.support),
      FiniteType.QuasiFiniteAt (Z.subschemeι ≫ f) ⟨x, hxZ⟩ ∧
        ∃ z : X, z ∈ Z.support ∧ z ∈ U ∧
          Specializes z x ∧ f z ≠ f x := sorry

end AlgebraicGeometry.Scheme.Hom

end
