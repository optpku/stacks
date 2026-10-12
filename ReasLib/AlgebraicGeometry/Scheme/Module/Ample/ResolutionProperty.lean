/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.Characterization
public import ReasLib.AlgebraicGeometry.Scheme.Module.ResolutionProperty

/-!
# Ample invertible modules and the resolution property

An ample invertible module on a scheme implies the resolution property.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme

/-- A scheme admitting an ample invertible module has the resolution property. -/
theorem hasResolutionProperty_of_hasAmpleInvertibleModule {X : Scheme.{u}}
    (hX : Modules.HasAmpleInvertibleModule X) : HasResolutionProperty X := sorry

end AlgebraicGeometry.Scheme
