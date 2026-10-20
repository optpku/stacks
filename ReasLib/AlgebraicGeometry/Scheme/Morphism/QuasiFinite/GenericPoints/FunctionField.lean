/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Birational.FunctionFieldDegree
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite.GenericPoints.FiniteNeighborhood

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

namespace FiniteFunctionFieldExtension

/-- A finite function-field extension induced by a dominant morphism of integral schemes gives
finite residue-field extensions at the generic points of the source. -/
theorem finiteResidues {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIntegral X] [IsIntegral Y] [IsDominant f]
    (hfinite : f.FiniteFunctionFieldExtension) :
    GenericPoints.finiteResidues f := sorry

end FiniteFunctionFieldExtension

/-- A proper dominant morphism of integral schemes that induces a finite extension of function
fields is finite over an open neighborhood of any target point whose local ring has dimension
one, provided the target is locally Noetherian. -/
theorem exists_isFinite_morphismRestrict_of_finiteFunctionFieldExtension
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsProper f] [IsDominant f] (ξ : Y)
    (hfinite : f.FiniteFunctionFieldExtension)
    (hξ : ringKrullDim (Y.presheaf.stalk ξ) = 1) :
    ∃ V : Y.Opens, ξ ∈ V ∧ IsFinite (f ∣_ V) := sorry

end AlgebraicGeometry.Scheme.Hom
