/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Radicial
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.UniversalHomeomorphism.Properties

/-!
# Radicial consequences of universal homeomorphisms

This leaf exposes the residue-field consequences of a universal
homeomorphism without forcing users of the topological API to rebuild the
bridge through universally injective morphisms.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

namespace UniversalHomeomorphism

variable {X Y : Scheme.{u}}

/-- A universal homeomorphism is radicial. -/
theorem radicial (f : X ⟶ Y) [UniversalHomeomorphism f] :
    Radicial f := sorry

/-- Universal homeomorphisms provide the canonical radicial instance. -/
instance instRadicial (f : X ⟶ Y) [UniversalHomeomorphism f] :
    Radicial f :=
  radicial f

/-- A universal homeomorphism induces purely inseparable extensions on all
residue fields. -/
theorem residueField_isPurelyInseparable
    (f : X ⟶ Y) (x : X) [UniversalHomeomorphism f] :
    IsPurelyInseparable (Y.residueField (f x)) (X.residueField x) := sorry

end UniversalHomeomorphism

end AlgebraicGeometry
