/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Morphism.Thickening.FirstOrder

/-!
# Strict morphisms of thickenings

Strictness is the epimorphicity condition on the ideal comparison map of a
morphism of thickenings.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Thickening.Hom

/-- A morphism of thickenings is strict when its ideal comparison map is epic. -/
def IsStrict {T U : Thickening.{u}} (g : T ⟶ U) : Prop :=
  Epi (idealMap g)

/-- Strictness is equivalent to epimorphicity of the ideal comparison map. -/
theorem isStrict_iff {T U : Thickening.{u}} (g : T ⟶ U) :
    IsStrict g ↔ Epi (idealMap g) := sorry

/-- For first-order thickenings, strictness is equivalent to epimorphicity of the
source ideal comparison map. -/
theorem isStrict_iff_sourceIdealMap {T U : Thickening.{u}}
    [IsFirstOrderThickening T.hom] [IsFirstOrderThickening U.hom] (g : T ⟶ U) :
    IsStrict g ↔ Epi (sourceIdealMap g) := sorry

end AlgebraicGeometry.RingedSpace.Thickening.Hom
