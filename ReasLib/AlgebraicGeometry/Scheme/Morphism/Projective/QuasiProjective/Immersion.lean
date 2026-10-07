module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.QuasiProjective.QuasiFinite

/-!
# Quasi-projectivity of immersions

This file records that a quasi-compact immersion of schemes is quasi-projective.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- A quasi-compact immersion of schemes is quasi-projective. -/
theorem IsImmersion.quasiProjective_of_quasiCompact
    {X S : Scheme.{u}} {f : X ⟶ S}
    (hf : IsImmersion f) (hqc : QuasiCompact f) :
    QuasiProjective f := sorry

/-- A quasi-compact immersion canonically carries a quasi-projective structure. -/
instance instQuasiProjectiveOfQuasiCompactImmersion
    {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [IsImmersion f] :
    QuasiProjective f :=
  IsImmersion.quasiProjective_of_quasiCompact inferInstance inferInstance

end AlgebraicGeometry
