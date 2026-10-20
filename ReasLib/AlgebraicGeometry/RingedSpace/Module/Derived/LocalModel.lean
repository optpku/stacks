/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpenSubspace.Derived
import Mathlib.Tactic.CrossRefAttribute

/-!
# Local complex models of derived modules

This file owns the source-independent pattern in which the restriction of a derived module to an
open subspace is represented by a complex satisfying an `ObjectProperty`.  Specializations such
as strictly perfect, bounded finite locally free, and bounded flat models belong in downstream
leaves.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleDerived.LocalModel

variable {X : RingedSpace.{u}}

/-- Complexes of modules on the open subspace `U` of `X`. -/
abbrev ComplexOn (X : RingedSpace.{u}) (U : Opens X.carrier) :=
  _root_.CochainComplex (Modules (X.restrict U.isOpenEmbedding)) ℤ

/-- The object property of derived modules whose restriction to `U` has a representative
satisfying `P`. -/
@[stacks 08CN "local model"]
def on (U : Opens X.carrier) (P : ObjectProperty (ComplexOn X U)) :
    ObjectProperty (ModuleDerived X) :=
  fun K ↦ ∃ E : ComplexOn X U,
    ∃ _ : (moduleRestrictionToOpenDerived X U).obj K ≅ DerivedCategory.Q.obj E, P E

/-- Membership in `on U P` is the existence of a `P`-representative for the canonical
restriction to `U`. -/
theorem mem_on_iff (U : Opens X.carrier) (P : ObjectProperty (ComplexOn X U))
    (K : ModuleDerived X) :
    on U P K ↔ ∃ E : ComplexOn X U,
      ∃ _ : (moduleRestrictionToOpenDerived X U).obj K ≅ DerivedCategory.Q.obj E, P E := sorry

/-- Enlarging the allowed property enlarges the local-model property. -/
theorem on_mono (U : Opens X.carrier) {P Q : ObjectProperty (ComplexOn X U)}
    (h : P ≤ Q) : on U P ≤ on U Q := sorry

/-- Having a `P`-model on `U` is invariant under isomorphism of derived modules. -/
instance on_isClosedUnderIsomorphisms
    (U : Opens X.carrier) (P : ObjectProperty (ComplexOn X U)) :
    (on U P).IsClosedUnderIsomorphisms := sorry

/-- The object property of derived modules admitting local `P`-models on an open cover. -/
@[stacks 08CN "local models on a cover"]
def onCover (P : ∀ U : Opens X.carrier, ObjectProperty (ComplexOn X U)) :
    ObjectProperty (ModuleDerived X) :=
  fun K ↦ ∃ (I : Type u) (U : I → Opens X.carrier), IsOpenCover U ∧
    ∀ i : I, on (U i) (P (U i)) K

/-- Membership in `onCover P` is the existence of an open cover carrying local `P`-models. -/
theorem mem_onCover_iff
    (P : ∀ U : Opens X.carrier, ObjectProperty (ComplexOn X U)) (K : ModuleDerived X) :
    onCover P K ↔ ∃ (I : Type u) (U : I → Opens X.carrier), IsOpenCover U ∧
      ∀ i : I, on (U i) (P (U i)) K := sorry

/-- Pointwise enlargement of the allowed local properties enlarges the corresponding
open-cover property. -/
theorem onCover_mono
    {P Q : ∀ U : Opens X.carrier, ObjectProperty (ComplexOn X U)}
    (h : ∀ U, P U ≤ Q U) : onCover P ≤ onCover Q := sorry

/-- Admitting local `P`-models on an open cover is invariant under isomorphism. -/
instance onCover_isClosedUnderIsomorphisms
    (P : ∀ U : Opens X.carrier, ObjectProperty (ComplexOn X U)) :
    (onCover P).IsClosedUnderIsomorphisms := sorry

end AlgebraicGeometry.RingedSpace.ModuleDerived.LocalModel
