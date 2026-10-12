/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.ClosedImmersion.Adjunction

@[expose] public section

/-! # Compatibility name for the derived internal Hom from the source structure sheaf. -/

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleDerived.ClosedImmersion

variable {X Z : RingedSpace.{u}} (i : Z ⟶ X)

/-- The K-injective total right-derived internal-Hom functor from `𝒪_Z`. -/
noncomputable abbrev rHomStructureSheaf
    (h_closed : Topology.IsClosedEmbedding i.hom.base)
    [Sheaf.IsLocallySurjective (RingedSpace.Hom.commRingSheafPushforwardMap i)] :
    RingedSpace.ModuleDerived X ⥤ RingedSpace.ModuleDerived Z :=
  rHomFromStructureSheaf i h_closed

end AlgebraicGeometry.RingedSpace.ModuleDerived.ClosedImmersion
