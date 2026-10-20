/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.GenericallyFinite.Integral
import StacksCheckRecall

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Lemma 29.51.7: for a dominant locally finite type morphism of integral schemes, the induced
function-field extension has transcendence degree zero if and only if it is finite-dimensional,
if and only if the morphism is finite between suitable nonempty affine opens, if and only if the
fiber over the target generic point consists only of the source generic point. -/
@[stacks 02NX] #check
  (AlgebraicGeometry.Scheme.Hom.genericallyFinite_tfae_of_isIntegral :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegral X] [IsIntegral Y]
      [LocallyOfFiniteType f] [IsDominant f],
      let _ : Algebra Y.functionField X.functionField :=
        f.functionFieldAlgebra f.map_genericPoint_eq_of_isDominant
      List.TFAE
        [ Algebra.trdeg Y.functionField X.functionField = 0
        , FiniteDimensional Y.functionField X.functionField
        , ∃ (U : X.Opens) (_ : Nonempty U) (V : Y.Opens) (_ : Nonempty V)
              (_ : IsAffineOpen U) (_ : IsAffineOpen V) (hUV : U ≤ f ⁻¹ᵁ V),
            IsFinite (f.resLE V U hUV)
        , f.base ⁻¹' ({genericPoint Y} : Set Y) = ({genericPoint X} : Set X)
        ])

/- Lemma 29.51.7 (conditional extension): if the morphism is quasi-compact or separated, the
preceding conditions are also equivalent to finiteness over the preimage of a nonempty affine
open of the target. -/
@[stacks 02NX] #check
  (AlgebraicGeometry.Scheme.Hom.genericallyFinite_tfae_of_isIntegral_of_quasiCompact_or_isSeparated :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegral X] [IsIntegral Y]
      [LocallyOfFiniteType f] [IsDominant f]
      (hqc_or_sep : QuasiCompact f ∨ IsSeparated f),
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
        ])
