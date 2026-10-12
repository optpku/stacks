/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.Topology.Semicontinuity.Defs
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.LocallyQuasiFinite
import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite.EtaleNeighborhood

/-!
# Semicontinuity of component counts for locally quasi-finite fibres
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.LocallyQuasiFinite

/-- The geometric fibre-component count of a separated, locally finite-type,
locally quasi-finite, universally open morphism is lower semicontinuous. -/
theorem lowerSemicontinuous_geometricFiberComponentCount
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] [LocallyQuasiFinite f]
    [IsSeparated f] [UniversallyOpen f] :
    LowerSemicontinuous f.geometricFiberComponentCount := sorry

end AlgebraicGeometry.LocallyQuasiFinite
