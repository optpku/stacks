module

public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite.Fiber
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite.GenericPoints

@[expose] public section

/-!
# Finite neighborhoods from generic quasi-finiteness

This module gives criteria ensuring that a proper morphism becomes finite over a neighborhood of
a target point with a low-dimensional Noetherian local ring.
-/

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}}

/-- A proper morphism whose generic residue-field extensions are finite becomes finite over an
open neighborhood of any target point with Noetherian local ring of dimension at most one. -/
@[stacks 0AB7]
theorem exists_isFinite_morphismRestrict_of_finiteGenericResidues
    (f : X ⟶ Y) [IsProper f] (y : Y)
    (hy_noetherian : IsNoetherianRing (Y.presheaf.stalk y))
    (hy_dim : ringKrullDim (Y.presheaf.stalk y) ≤ 1)
    (hgeneric : GenericPoints.finiteResidues f) :
    ∃ V : Y.Opens, y ∈ V ∧ IsFinite (f ∣_ V) := sorry

/-- A proper morphism whose generic residue-field extensions are algebraic becomes finite over an
open neighborhood of any target point with Noetherian local ring of dimension at most one. -/
@[stacks 0AB7]
theorem exists_isFinite_morphismRestrict_of_algebraicGenericResidues
    (f : X ⟶ Y) [IsProper f] (y : Y)
    (hy_noetherian : IsNoetherianRing (Y.presheaf.stalk y))
    (hy_dim : ringKrullDim (Y.presheaf.stalk y) ≤ 1)
    (hgeneric : GenericPoints.algebraicResidues f) :
    ∃ V : Y.Opens, y ∈ V ∧ IsFinite (f ∣_ V) := sorry

/-- A proper morphism with finite residue-field extensions at the generic points specializing over
`y` becomes finite over an open neighborhood of `y` when its local ring is Noetherian of dimension
at most one. -/
@[stacks 0AB7]
theorem exists_isFinite_morphismRestrict_of_finiteGenericResiduesOver
    (f : X ⟶ Y) [IsProper f] (y : Y)
    (hy_noetherian : IsNoetherianRing (Y.presheaf.stalk y))
    (hy_dim : ringKrullDim (Y.presheaf.stalk y) ≤ 1)
    (hgeneric : GenericPoints.finiteResiduesOver f y) :
    ∃ V : Y.Opens, y ∈ V ∧ IsFinite (f ∣_ V) := sorry

/-- A proper morphism with algebraic residue-field extensions at the generic points specializing
over `y` becomes finite over an open neighborhood of `y` when its local ring is Noetherian of
dimension at most one. -/
@[stacks 0AB7]
theorem exists_isFinite_morphismRestrict_of_algebraicGenericResiduesOver
    (f : X ⟶ Y) [IsProper f] (y : Y)
    (hy_noetherian : IsNoetherianRing (Y.presheaf.stalk y))
    (hy_dim : ringKrullDim (Y.presheaf.stalk y) ≤ 1)
    (hgeneric : GenericPoints.algebraicResiduesOver f y) :
    ∃ V : Y.Opens, y ∈ V ∧ IsFinite (f ∣_ V) := sorry

/-- A proper morphism that is quasi-finite at every generic point of its source becomes finite
over an open neighborhood of any target point with Noetherian local ring of dimension at most
one. -/
@[stacks 0AB7]
theorem exists_isFinite_morphismRestrict_of_quasiFiniteAtGenericPoints
    (f : X ⟶ Y) [IsProper f] (y : Y)
    (hy_noetherian : IsNoetherianRing (Y.presheaf.stalk y))
    (hy_dim : ringKrullDim (Y.presheaf.stalk y) ≤ 1)
    (hgeneric : GenericPoints.quasiFinite f) :
    ∃ V : Y.Opens, y ∈ V ∧ IsFinite (f ∣_ V) := sorry

/-- A proper morphism to a locally Noetherian scheme with dense quasi-finite locus becomes finite
over an open neighborhood of any target point with Noetherian local ring of dimension at most
one. -/
@[stacks 0AB7]
theorem exists_isFinite_morphismRestrict_of_denseQuasiFiniteLocus
    (f : X ⟶ Y) [IsProper f] [IsLocallyNoetherian Y] (y : Y)
    (hy_noetherian : IsNoetherianRing (Y.presheaf.stalk y))
    (hy_dim : ringKrullDim (Y.presheaf.stalk y) ≤ 1)
    (hdense : QuasiFinite.hasDenseLocus f) :
    ∃ V : Y.Opens, y ∈ V ∧ IsFinite (f ∣_ V) := sorry

end AlgebraicGeometry.Scheme.Hom
