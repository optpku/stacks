/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.K0.CoherentSupport

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.K0'WithSupport

/- Compatibility check for coherent pushforward to supported coherent K₀. -/
#check (AlgebraicGeometry.Scheme.K0'WithSupport.closedPushforward :
  ∀ {X Z : Scheme.{u}} [IsLocallyNoetherian X]
      (i : Z ⟶ X) [IsClosedImmersion i],
    @K0' Z (LocallyOfFiniteType.isLocallyNoetherian i) →+
      K0'WithSupport X (Set.range i.base))

end AlgebraicGeometry.Scheme.K0'WithSupport
