/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.AlgebraicGeometry.Scheme.GenericPoints
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ResidueField.Extension

@[expose] public section

/-!
# Quasi-finiteness from generic points

This module collects residue-field and finite-type quasi-finiteness conditions at generic points
of irreducible components, together with criteria propagating them over low-dimensional points.
-/

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}}

namespace GenericPoints

/-- Every generic point of an irreducible component has finite residue-field extension along
`f`. -/
def finiteResidues (f : X ⟶ Y) : Prop :=
  ∀ η : X, η ∈ genericPoints X → ResidueField.finiteAt f η

/-- Every generic point above a specialization of `y` has finite residue-field extension along
`f`. -/
def finiteResiduesOver (f : X ⟶ Y) (y : Y) : Prop :=
  ∀ η : X, η ∈ genericPoints X → f η ⤳ y →
    ResidueField.finiteAt f η

/-- Every generic point of an irreducible component has algebraic residue-field extension along
`f`. -/
def algebraicResidues (f : X ⟶ Y) : Prop :=
  ∀ η : X, η ∈ genericPoints X → ResidueField.algebraicAt f η

/-- Every generic point above a specialization of `y` has algebraic residue-field extension
along `f`. -/
def algebraicResiduesOver (f : X ⟶ Y) (y : Y) : Prop :=
  ∀ η : X, η ∈ genericPoints X → f η ⤳ y →
    ResidueField.algebraicAt f η

/-- The morphism `f` is finite-type quasi-finite at every generic point of an irreducible
component of its source. -/
def quasiFinite (f : X ⟶ Y) : Prop :=
  ∀ η : X, η ∈ genericPoints X → FiniteType.QuasiFiniteAt f η

end GenericPoints

namespace QuasiFinite

/-- The finite-type quasi-finite locus of `f` is dense in its source. -/
def hasDenseLocus (f : X ⟶ Y) : Prop :=
  Dense {x : X | FiniteType.QuasiFiniteAt f x}

/-- Finite residue-field extensions at generic points imply finite-type quasi-finiteness at every
point over a Noetherian target point of dimension at most one. -/
@[stacks 0AB6]
theorem at_of_finiteGenericResidues
    (f : X ⟶ Y) [LocallyOfFiniteType f] (y : Y)
    (hy_noetherian : IsNoetherianRing (Y.presheaf.stalk y))
    (hy_dim : ringKrullDim (Y.presheaf.stalk y) ≤ 1)
    (hgeneric : GenericPoints.finiteResidues f) :
    ∀ x : X, f x = y → FiniteType.QuasiFiniteAt f x := sorry

/-- Algebraic residue-field extensions at generic points imply finite-type quasi-finiteness at
every point over a Noetherian target point of dimension at most one. -/
@[stacks 0AB6]
theorem at_of_algebraicGenericResidues
    (f : X ⟶ Y) [LocallyOfFiniteType f] (y : Y)
    (hy_noetherian : IsNoetherianRing (Y.presheaf.stalk y))
    (hy_dim : ringKrullDim (Y.presheaf.stalk y) ≤ 1)
    (hgeneric : GenericPoints.algebraicResidues f) :
    ∀ x : X, f x = y → FiniteType.QuasiFiniteAt f x := sorry

/-- Finite residue-field extensions at generic points specializing to `y` imply finite-type
quasi-finiteness at every point over `y`. -/
@[stacks 0AB6]
theorem at_of_finiteGenericResiduesOver
    (f : X ⟶ Y) [LocallyOfFiniteType f] (y : Y)
    (hy_noetherian : IsNoetherianRing (Y.presheaf.stalk y))
    (hy_dim : ringKrullDim (Y.presheaf.stalk y) ≤ 1)
    (hgeneric : GenericPoints.finiteResiduesOver f y) :
    ∀ x : X, f x = y → FiniteType.QuasiFiniteAt f x := sorry

/-- Algebraic residue-field extensions at generic points specializing to `y` imply finite-type
quasi-finiteness at every point over `y`. -/
@[stacks 0AB6]
theorem at_of_algebraicGenericResiduesOver
    (f : X ⟶ Y) [LocallyOfFiniteType f] (y : Y)
    (hy_noetherian : IsNoetherianRing (Y.presheaf.stalk y))
    (hy_dim : ringKrullDim (Y.presheaf.stalk y) ≤ 1)
    (hgeneric : GenericPoints.algebraicResiduesOver f y) :
    ∀ x : X, f x = y → FiniteType.QuasiFiniteAt f x := sorry

/-- Finite-type quasi-finiteness at generic points of irreducible components implies the same at
every point over a Noetherian target point of dimension at most one. -/
@[stacks 0AB6]
theorem at_of_genericPoints
    (f : X ⟶ Y) [LocallyOfFiniteType f] (y : Y)
    (hy_noetherian : IsNoetherianRing (Y.presheaf.stalk y))
    (hy_dim : ringKrullDim (Y.presheaf.stalk y) ≤ 1)
    (hgeneric : GenericPoints.quasiFinite f) :
    ∀ x : X, f x = y → FiniteType.QuasiFiniteAt f x := sorry

/-- A dense finite-type quasi-finite locus implies finite-type quasi-finiteness at every point
over a Noetherian target point of dimension at most one. -/
@[stacks 0AB6]
theorem at_of_denseLocus
    (f : X ⟶ Y) [LocallyOfFiniteType f] [IsLocallyNoetherian Y] (y : Y)
    (hy_noetherian : IsNoetherianRing (Y.presheaf.stalk y))
    (hy_dim : ringKrullDim (Y.presheaf.stalk y) ≤ 1)
    (hdense : hasDenseLocus f) :
    ∀ x : X, f x = y → FiniteType.QuasiFiniteAt f x := sorry

end QuasiFinite

end AlgebraicGeometry.Scheme.Hom
