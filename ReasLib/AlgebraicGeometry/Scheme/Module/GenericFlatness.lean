/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation
public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat

/-!
# Generic flatness

This module records the simultaneous generic-flatness conditions for a scheme morphism and a
module sheaf, together with the existence theorem over an integral base.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X S : Scheme.{u}}

/-- An open `U ⊆ S` is a generic-flatness locus for `f : X ⟶ S` and `ℱ : X.Modules` when the
restricted morphism is flat and of finite presentation, while the restricted module is flat over
the base and of finite presentation. -/
def GenericFlatnessOn (f : X ⟶ S) (ℱ : X.Modules) (U : S.Opens) : Prop :=
  Scheme.Hom.FinitePresentation (f ∣_ U) ∧
    AlgebraicGeometry.Flat (f ∣_ U) ∧
    flatOver (ℱ.restrict ((f ⁻¹ᵁ U).ι)) (f ∣_ U) ∧
    (ℱ.restrict ((f ⁻¹ᵁ U).ι)).IsFinitePresentation

/-- The generic-flatness predicate is equivalent to the four conditions on the restricted
morphism and restricted module. -/
theorem genericFlatnessOn_iff (f : X ⟶ S) (ℱ : X.Modules) (U : S.Opens) :
    GenericFlatnessOn f ℱ U ↔
      Scheme.Hom.FinitePresentation (f ∣_ U) ∧
        AlgebraicGeometry.Flat (f ∣_ U) ∧
        flatOver (ℱ.restrict ((f ⁻¹ᵁ U).ι)) (f ∣_ U) ∧
        (ℱ.restrict ((f ⁻¹ᵁ U).ι)).IsFinitePresentation := sorry

/-- A finite-type morphism to an integral scheme and a finite-type quasicoherent module admit a
dense open on which the morphism and module are flat and of finite presentation. -/
theorem exists_dense_open_genericFlatness
    (f : X ⟶ S) [IsIntegral S] [Scheme.Hom.FiniteType f]
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] [ℱ.IsFiniteType] :
    ∃ U : S.Opens, Dense (U : Set S) ∧ GenericFlatnessOn f ℱ U := sorry

/-- A finite-type morphism to a reduced scheme and a finite-type quasicoherent module admit a
dense open on which the morphism and module are flat and of finite presentation. -/
theorem exists_dense_open_genericFlatness_of_reduced
    (f : X ⟶ S) [IsReduced S] [Scheme.Hom.FiniteType f]
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] [ℱ.IsFiniteType] :
    ∃ U : S.Opens, Dense (U : Set S) ∧ GenericFlatnessOn f ℱ U := sorry

end AlgebraicGeometry.Scheme.Modules
