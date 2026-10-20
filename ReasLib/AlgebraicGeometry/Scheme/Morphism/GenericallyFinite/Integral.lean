/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FunctionField
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.GenericallyFinite.DenseOpen

/-!
# Generically finite morphisms of integral schemes

This file characterizes generically finite dominant morphisms of integral schemes in terms of
their induced function-field extensions, finite restrictions to affine opens, and fibers over
generic points.
-/

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- For a dominant locally finite type morphism of integral schemes, the induced function-field
extension has transcendence degree zero if and only if it is finite-dimensional, if and only if
the morphism is finite between suitable nonempty affine opens, if and only if the fiber over the
target generic point consists only of the source generic point. -/
theorem genericallyFinite_tfae_of_isIntegral
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegral X] [IsIntegral Y]
    [LocallyOfFiniteType f] [IsDominant f] :
    -- Local instance justification (instance diamond): distinct morphisms can induce competing algebra structures on the same pair of function fields.
    let _ : Algebra Y.functionField X.functionField :=
      f.functionFieldAlgebra f.map_genericPoint_eq_of_isDominant
    List.TFAE
      [ Algebra.trdeg Y.functionField X.functionField = 0
      , FiniteDimensional Y.functionField X.functionField
      , ∃ (U : X.Opens) (_ : Nonempty U) (V : Y.Opens) (_ : Nonempty V)
            (_ : IsAffineOpen U) (_ : IsAffineOpen V) (hUV : U ≤ f ⁻¹ᵁ V),
          IsFinite (f.resLE V U hUV)
      , f.base ⁻¹' ({genericPoint Y} : Set Y) = ({genericPoint X} : Set X)
      ] := sorry

/-- If a dominant locally finite type morphism of integral schemes is quasi-compact or
separated, the equivalent generically finite conditions are also equivalent to finiteness over
the preimage of a nonempty affine open of the target. -/
theorem genericallyFinite_tfae_of_isIntegral_of_quasiCompact_or_isSeparated
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegral X] [IsIntegral Y]
    [LocallyOfFiniteType f] [IsDominant f]
    (hqc_or_sep : QuasiCompact f ∨ IsSeparated f) :
    -- Local instance justification (instance diamond): distinct morphisms can induce competing algebra structures on the same pair of function fields.
    let _ : Algebra Y.functionField X.functionField :=
      f.functionFieldAlgebra f.map_genericPoint_eq_of_isDominant
    List.TFAE
      [ Algebra.trdeg Y.functionField X.functionField = 0
      , FiniteDimensional Y.functionField X.functionField
      , ∃ (U : X.Opens) (_ : Nonempty U) (V : Y.Opens) (_ : Nonempty V)
            (_ : IsAffineOpen U) (_ : IsAffineOpen V) (hUV : U ≤ f ⁻¹ᵁ V),
          IsFinite (f.resLE V U hUV)
      , f.base ⁻¹' ({genericPoint Y} : Set Y) = ({genericPoint X} : Set X)
      , ∃ (V : Y.Opens) (_ : Nonempty V) (_ : IsAffineOpen V), IsFinite (f ∣_ V)
      ] := sorry

end AlgebraicGeometry.Scheme.Hom
