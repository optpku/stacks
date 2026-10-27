/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.LocallyFinite
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Topology
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Integral
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Meromorphic.Order


/-!
# Local finiteness of prime divisors of a regular meromorphic section

On a locally Noetherian integral algebraic space, the prime divisors at which a
regular meromorphic section of an invertible module fails to lie in `L_ξ`, and
those along which its order is nonzero, form locally finite families in
`Points X`. Here `L_ξ = (Modules.pullback (fromHenselization X ξ)).obj L`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} (X : AlgebraicSpace S)
variable [IsLocallyNoetherian X] [IsIntegral X]

/-- The prime divisors at which a regular meromorphic section of an invertible
module on a locally Noetherian integral space is not regular form a locally finite family. -/
theorem locallyFinite_primeDivisors_regularMeromorphicSection_not_regularAt
    {L : X.Modules} [isInvertibleObject L]
    (s : meromorphicSections X L) (hs : IsRegularMeromorphicSection X L s) :
    LocallyFinite fun Z : PrimeDivisor X ↦
      {x | ¬ MeromorphicSection.IsRegularAt s Z.genericPoint ∧ x ∈ Z.pointsSet} := sorry

/-- The prime divisors along which a regular meromorphic section of an invertible
module on a locally Noetherian integral space has nonzero order form a locally finite family. -/
theorem locallyFinite_regularMeromorphicSectionOrder_ne_zero
    {L : X.Modules} [isInvertibleObject L]
    (s : meromorphicSections X L) (hs : IsRegularMeromorphicSection X L s) :
    LocallyFinite fun Z : PrimeDivisor X ↦
      if MeromorphicSection.ord s hs Z = 0 then (∅ : Set (Points X)) else Z.pointsSet := sorry

end AlgebraicGeometry.AlgebraicSpace
