/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Kaehler.JacobiZariski
public import ReasLib.RingTheory.LocalRing.ResidueField.Cotangent
public import ReasLib.RingTheory.LocalRing.ResidueField.Kaehler
import Mathlib.Tactic.CrossRefAttribute

/-!
# Residue-field Jacobi--Zariski maps

@stack 0DYH

This leaf connects the generic Jacobi--Zariski boundary map to the cotangent
space of a residue field.  It deliberately keeps the maps universe-polymorphic;
the `ModuleCat` row is provided by a separate companion leaf.
-/

@[expose] public section

open Algebra
open IsLocalRing
open KaehlerDifferential
open scoped TensorProduct

universe u v

namespace Algebra.H1Cotangent

namespace ResidueField

noncomputable section

variable {A : Type u} {B : Type v}
variable [CommRing A] [CommRing B] [Algebra A B]
variable [IsLocalRing B]

variable (A B)

/-- The first nonzero arrow in the residue-field Jacobi--Zariski sequence. -/
@[stacks 0DYH "residue-field H₁-to-cotangent map"]
noncomputable def toCotangent :
    H1Cotangent A (ResidueField B) →ₗ[ResidueField B] CotangentSpace B :=
  (IsLocalRing.ResidueField.h1CotangentEquiv B).toLinearMap.comp
    (Algebra.H1Cotangent.map A B (ResidueField B) (ResidueField B))

/-- Evaluation of the first residue-field Jacobi--Zariski arrow through its two canonical maps. -/
@[simp, stacks 0DYH "residue-field H₁-to-cotangent evaluation"]
theorem toCotangent_apply (x : H1Cotangent A (ResidueField B)) :
    toCotangent A B x =
      IsLocalRing.ResidueField.h1CotangentEquiv B
        (Algebra.H1Cotangent.map A B (ResidueField B) (ResidueField B) x) := sorry

/-- Compatibility of the residue-field identification with the Jacobi--Zariski boundary map. -/
@[stacks 0DYH "residue H₁/conormal compatibility"]
theorem conormal_comp_h1CotangentEquiv :
    (IsLocalRing.ResidueField.conormal (A := A) (B := B)).comp
        (IsLocalRing.ResidueField.h1CotangentEquiv B).toLinearMap =
      Algebra.H1Cotangent.δ A B (ResidueField B) := sorry

/-- The first two nonzero arrows of the residue-field Jacobi--Zariski sequence are exact. -/
@[stacks 0DYH "residue H₁-to-conormal exactness"]
theorem toCotangent_exact :
    Function.Exact (toCotangent A B)
      (IsLocalRing.ResidueField.conormal (A := A) (B := B)) := sorry

/-- Injectivity of the residue-field Jacobi--Zariski arrow is equivalent to injectivity of the
underlying homology map, because `h1CotangentEquiv` is a linear equivalence. -/
@[stacks 0DYH "residue H₁ map/cotangent injectivity criterion"]
theorem toCotangent_injective_iff :
    Function.Injective (toCotangent A B) ↔
      Function.Injective
        (Algebra.H1Cotangent.map A B (ResidueField B) (ResidueField B)) := sorry

end

end ResidueField

end Algebra.H1Cotangent
