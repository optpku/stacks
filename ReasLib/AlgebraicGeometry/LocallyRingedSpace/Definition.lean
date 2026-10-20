module

public import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
public import ReasLib.AlgebraicGeometry.RingedSpace.Definition
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Structure-sheaf maps of locally ringed spaces

This foundational leaf exposes the structure-sheaf map of a locally ringed-space morphism
without importing ideal subobjects, closed immersions, or scheme-specific constructions.
-/

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry.LocallyRingedSpace.Hom

/-- The structure-sheaf morphism `𝒪_X ⟶ i_* 𝒪_Z` of a locally ringed-space morphism. -/
@[stacks 01HK "structure-sheaf pushforward map"]
noncomputable abbrev commRingSheafPushforwardMap
    {X Z : LocallyRingedSpace.{u}} (i : Z ⟶ X) :=
  RingedSpace.Hom.commRingSheafPushforwardMap i.toShHom

end AlgebraicGeometry.LocallyRingedSpace.Hom
