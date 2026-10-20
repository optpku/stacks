/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.FunctionField
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Normalization.Nagata

/-!
# Normalization in finite extensions of function fields

This module provides the canonical map from the spectrum of a function-field extension to an
integral scheme and records finiteness properties of its relative normalization.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.FunctionFieldExtension

/-- The canonical morphism `Spec L ⟶ S` associated to an extension `L` of the function field
of an integral scheme `S`. -/
noncomputable def map
    (S : Scheme.{u}) [IsIntegral S] (L : Type u) [Field L]
    [Algebra S.functionField L] :
    Spec (CommRingCat.of L) ⟶ S :=
  FieldExtension.specMap S.functionField L ≫ S.fromSpecStalk (genericPoint S)

/-- The function-field extension map factors through the spectrum of the function field. -/
theorem map_eq
    (S : Scheme.{u}) [IsIntegral S] (L : Type u) [Field L]
    [Algebra S.functionField L] :
    map S L =
      FieldExtension.specMap S.functionField L ≫ S.fromSpecStalk (genericPoint S) := sorry

/-- The normalization of a Nagata integral scheme in a finite extension of its function field
is finite over the original scheme. -/
instance instIsFiniteFromNormalization
    (S : Scheme.{u}) [IsIntegral S] [Scheme.Nagata S]
    (L : Type u) [Field L] [Algebra S.functionField L]
    [FiniteDimensional S.functionField L] :
    IsFinite (map S L).fromNormalization := sorry

/-- The normalization of a Nagata integral scheme in a finite extension of its function field
is locally Noetherian. -/
instance instIsLocallyNoetherianNormalization
    (S : Scheme.{u}) [IsIntegral S] [Scheme.Nagata S]
    (L : Type u) [Field L] [Algebra S.functionField L]
    [FiniteDimensional S.functionField L] :
    IsLocallyNoetherian (map S L).normalization := sorry

end AlgebraicGeometry.Scheme.FunctionFieldExtension
