/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.List.TFAE
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Integral
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.ResidueFieldTrdeg
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Finite
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.LocallyQuasiFinite.Locality
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.Support
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ResidueField.Morphism
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Point.GenericPoints.Dominant

/-! # Generically finite morphisms of integral algebraic spaces -/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- For a dominant locally finite type morphism between integral algebraic spaces,
the generic residue-field, affine restriction, quasi-finiteness, and singleton
generic-fibre conditions are equivalent. -/
theorem genericallyFinite_tfae {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) [LocallyOfFiniteType f]
    [Dominant f] {x : Points X} (hx : x ∈ genericPoints X) :
    List.TFAE
      [ residueFieldTrdegAt f x = 0
      , FiniteDimensional (Y.residueField (Points.map f x)) (X.residueField x)
      , ∃ (U : OpenSubspace X) (V : OpenSubspace Y) (g : U.X ⟶ V.X),
          U.pointsSet.Nonempty ∧ V.pointsSet.Nonempty ∧ IsAffine U.X ∧
            IsAffine V.X ∧ g ≫ V.ι = U.ι ≫ f ∧ IsFinite g
      , QuasiFiniteAt f x
      , Points.map f ⁻¹' {Points.map f x} = {x} ] :=
  sorry

/-- If a dominant locally finite type morphism between integral algebraic spaces
is quasi-compact or separated, the preceding conditions are also equivalent to
finiteness over a nonempty affine open of the target. -/
theorem genericallyFinite_tfae_of_quasiCompact_or_separated
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [LocallyOfFiniteType f] [Dominant f] {x : Points X}
    (hx : x ∈ genericPoints X) (hqc_or_sep : QuasiCompact f ∨ Separated f) :
    List.TFAE
      [ residueFieldTrdegAt f x = 0
      , FiniteDimensional (Y.residueField (Points.map f x)) (X.residueField x)
      , ∃ (U : OpenSubspace X) (V : OpenSubspace Y) (g : U.X ⟶ V.X),
          U.pointsSet.Nonempty ∧ V.pointsSet.Nonempty ∧ IsAffine U.X ∧
            IsAffine V.X ∧ g ≫ V.ι = U.ι ≫ f ∧ IsFinite g
      , QuasiFiniteAt f x
      , Points.map f ⁻¹' {Points.map f x} = {x}
      , ∃ V : OpenSubspace Y,
          V.pointsSet.Nonempty ∧ IsAffine V.X ∧
            IsFinite (pullback.snd f V.ι) ] :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
