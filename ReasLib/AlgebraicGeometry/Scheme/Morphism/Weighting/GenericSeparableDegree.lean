/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Weighting
public import ReasLib.AlgebraicGeometry.Scheme.Unibranch
public import ReasLib.RingTheory.LocalRing.Unibranch.StrictHenselization
public import ReasLib.RingTheory.RingHom.Fiber.GenericSeparableDegree

/-!
# Generic-separable-degree weightings

Locally finite-type, locally quasi-finite morphisms to locally Noetherian,
geometrically unibranch schemes admit a weighting computed by generic
separable degrees on stalks.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A locally finite-type, locally quasi-finite morphism to a geometrically
unibranch, locally Noetherian scheme admits a nonnegative weighting whose
value at every point is the generic separable degree of the induced map on
strict henselizations. -/
@[stacks 0F3E]
theorem exists_genericSepDegreeWeighting {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [LocallyQuasiFinite f] [IsLocallyNoetherian Y]
    (hY : Y.isGeometricallyUnibranch) :
    ∃ w : X → ℕ, f.IsWeighting (fun x ↦ (w x : ℤ)) ∧
      ∀ x : X, RingHom.IsGenericSepDegree (f.stalkMap x).hom
        (LocallyOfFiniteType.stalkMap f x) (f.quasiFiniteAt x) (w x) := sorry

end AlgebraicGeometry.Scheme.Hom
