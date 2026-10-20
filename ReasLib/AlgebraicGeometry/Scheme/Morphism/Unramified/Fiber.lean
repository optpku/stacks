/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ResidueField
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.OverField.FiniteSeparableCoproduct

/-!
# Fibres of unramified morphisms

This file characterizes unramified schemes over a field and describes the
finite-separable fibres and residue-field extensions of unramified morphisms.
-/

@[expose] public section

open CategoryTheory

universe u

noncomputable section

namespace AlgebraicGeometry

/-- A scheme over a field is unramified over that field if and only if it admits a presentation
as a coproduct of spectra of finite separable field extensions. -/
theorem unramified_iff_schemeAsDisjointUnionOfSpecFiniteSeparable
    {k : Type u} [Field k] (X : SchemeOverField k) :
    Unramified X.hom ↔ Nonempty (SchemeAsDisjointUnionOfSpecFiniteSeparable k X) := sorry

/-- Every fibre of an unramified morphism admits a presentation as a coproduct of spectra of
finite separable extensions of the corresponding residue field. -/
theorem fiber_schemeAsDisjointUnionOfSpecFiniteSeparable_of_unramified
    {X S : Scheme.{u}} (f : X ⟶ S) [Unramified f] (s : S) :
    Nonempty
      (SchemeAsDisjointUnionOfSpecFiniteSeparable (S.residueField s)
        (Over.mk (f.fiberOverSpecResidueField s).hom)) := sorry

namespace Scheme.Hom

/-- Every fibre of a scheme morphism is a disjoint union of spectra of finite separable
extensions of the corresponding residue field. -/
def FibersAreDisjointUnionOfSpecFiniteSeparable {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  ∀ s : S,
    Nonempty
      (SchemeAsDisjointUnionOfSpecFiniteSeparable (S.residueField s)
        (Over.mk (f.fiberToSpecResidueField s)))

/-- An unramified morphism has finite-separable spectral presentations of all its fibres. -/
theorem fibersAreDisjointUnionOfSpecFiniteSeparable_of_unramified
    {X S : Scheme.{u}} (f : X ⟶ S) [Unramified f] :
    f.FibersAreDisjointUnionOfSpecFiniteSeparable :=
  fiber_schemeAsDisjointUnionOfSpecFiniteSeparable_of_unramified f

end Scheme.Hom

/-- The residue-field extension induced by an unramified morphism at any point is finite and
separable. -/
theorem residueField_finite_separable_of_unramified
    {X S : Scheme.{u}} (f : X ⟶ S) [Unramified f] (x : X) :
    FiniteDimensional (S.residueField (f x)) (X.residueField x) ∧
      Algebra.IsSeparable (S.residueField (f x)) (X.residueField x) := sorry

/-- A locally finite type morphism whose fibres all have finite-separable spectral presentations
is unramified. -/
theorem unramified_of_fiber_schemeAsDisjointUnionOfSpecFiniteSeparable
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (hfiber : f.FibersAreDisjointUnionOfSpecFiniteSeparable) :
    Unramified f := sorry

/-- A locally finite presentation morphism whose fibres all have finite-separable spectral
presentations is G-unramified. -/
theorem gUnramified_of_fiber_schemeAsDisjointUnionOfSpecFiniteSeparable
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f]
    (hfiber : f.FibersAreDisjointUnionOfSpecFiniteSeparable) :
    GUnramified f := sorry

end AlgebraicGeometry
