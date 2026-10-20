/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Complex.StrictlyPerfect.LocalHomotopy
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpenSubspace.Derived
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Local representatives of derived morphisms on ringed spaces

This leaf is the open-subspace facade for the bundled ringed-site representation API.  The
comparison square is packaged once as `IsRepresentedOn`; point-neighborhood and null-homotopy
views are separate projections, so downstream arguments do not repeat the four comparison terms.
-/

open AlgebraicGeometry
open CategoryTheory
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.CochainComplex

variable {X : RingedSpace.{u}}

/-- A derived morphism is represented on an open `U` by a chain map and the canonical derived
restriction comparison square. -/
@[stacks 08C9 "open-subspace derived representation"]
def IsRepresentedOn
    {E F : _root_.CochainComplex (Modules X) ℤ}
    (α : DerivedCategory.Q.obj E ⟶ DerivedCategory.Q.obj F)
    (U : Opens X.carrier) : Prop :=
  ∃ β : (moduleRestrictionComplexToOpen X U).obj E ⟶
      (moduleRestrictionComplexToOpen X U).obj F,
    CommSq
      ((moduleRestrictionToOpenDerived X U).map α)
      (moduleRestrictionToOpenDerivedFactors X U E).hom
      (moduleRestrictionToOpenDerivedFactors X U F).hom
      (DerivedCategory.Q.map β)

/-- A derived morphism is represented locally at a point when it is represented on a
point-containing open neighborhood. -/
@[stacks 08C9 "point-neighborhood derived representation"]
def IsLocallyRepresentedAt
    {E F : _root_.CochainComplex (Modules X) ℤ}
    (α : DerivedCategory.Q.obj E ⟶ DerivedCategory.Q.obj F) (x : X) : Prop :=
  ∃ U : Opens X.carrier, x ∈ U ∧ IsRepresentedOn α U

/-- The open representation predicate unfolds to its canonical comparison square. -/
theorem isRepresentedOn_iff
    {E F : _root_.CochainComplex (Modules X) ℤ}
    (α : DerivedCategory.Q.obj E ⟶ DerivedCategory.Q.obj F) (U : Opens X.carrier) :
    IsRepresentedOn α U ↔
      ∃ β : (moduleRestrictionComplexToOpen X U).obj E ⟶
          (moduleRestrictionComplexToOpen X U).obj F,
        CommSq
          ((moduleRestrictionToOpenDerived X U).map α)
          (moduleRestrictionToOpenDerivedFactors X U E).hom
          (moduleRestrictionToOpenDerivedFactors X U F).hom
          (DerivedCategory.Q.map β) := sorry

/-- The point-local representation predicate unfolds to the open-neighborhood criterion. -/
theorem isLocallyRepresentedAt_iff
    {E F : _root_.CochainComplex (Modules X) ℤ}
    (α : DerivedCategory.Q.obj E ⟶ DerivedCategory.Q.obj F) (x : X) :
    IsLocallyRepresentedAt α x ↔
      ∃ U : Opens X.carrier, x ∈ U ∧
        ∃ β : (moduleRestrictionComplexToOpen X U).obj E ⟶
            (moduleRestrictionComplexToOpen X U).obj F,
          CommSq
            ((moduleRestrictionToOpenDerived X U).map α)
            (moduleRestrictionToOpenDerivedFactors X U E).hom
            (moduleRestrictionToOpenDerivedFactors X U F).hom
            (DerivedCategory.Q.map β) := sorry

namespace IsStrictlyPerfect

namespace Representation

/-- Lemma 20.46.8 (1): a derived morphism from a strictly perfect complex is represented on an
open cover. -/
@[stacks 08C9 "open-cover derived representation"]
theorem cover
    {E F : _root_.CochainComplex (Modules X) ℤ}
    (hE : _root_.SheafOfModules.CochainComplex.IsStrictlyPerfect E)
    (α : DerivedCategory.Q.obj E ⟶ DerivedCategory.Q.obj F) :
    ∃ (I : Type u) (U : I → Opens X.carrier), IsOpenCover U ∧
      ∀ i : I, IsRepresentedOn α (U i) := sorry

/-- Lemma 20.46.8 (1), point-neighborhood representation view. -/
@[stacks 08C9 "point-neighborhood derived representation"]
theorem atPoint
    {E F : _root_.CochainComplex (Modules X) ℤ}
    (hE : _root_.SheafOfModules.CochainComplex.IsStrictlyPerfect E)
    (α : DerivedCategory.Q.obj E ⟶ DerivedCategory.Q.obj F) (x : X) :
    IsLocallyRepresentedAt α x := sorry

/-- The equality view of the local representative, with the comparison isomorphisms moved to the
outside of the derived-category map. -/
@[stacks 08C9 "derived representation equality view"]
theorem at_eq
    {E F : _root_.CochainComplex (Modules X) ℤ}
    (hE : _root_.SheafOfModules.CochainComplex.IsStrictlyPerfect E)
    (α : DerivedCategory.Q.obj E ⟶ DerivedCategory.Q.obj F) (x : X) :
    ∃ U : Opens X.carrier, x ∈ U ∧
      ∃ β : (moduleRestrictionComplexToOpen X U).obj E ⟶
          (moduleRestrictionComplexToOpen X U).obj F,
        (moduleRestrictionToOpenDerived X U).map α =
          (moduleRestrictionToOpenDerivedFactors X U E).hom ≫
            DerivedCategory.Q.map β ≫
            (moduleRestrictionToOpenDerivedFactors X U F).inv := sorry

end Representation

namespace NullHomotopy

/-- Lemma 20.46.8 (2): a strictly perfect chain map which is zero in the derived category is
null-homotopic on an open cover. -/
@[stacks 08C9 "derived-zero open-cover null homotopy"]
theorem cover_of_derived_zero
    {E F : _root_.CochainComplex (Modules X) ℤ}
    (hE : _root_.SheafOfModules.CochainComplex.IsStrictlyPerfect E)
    (α : E ⟶ F) (hα : DerivedCategory.Q.map α = 0) :
    ∃ (I : Type u) (U : I → Opens X.carrier), IsOpenCover U ∧
      ∀ i : I, IsNullHomotopicOn α (U i) := sorry

/-- Lemma 20.46.8 (2), point-neighborhood null-homotopy view. -/
@[stacks 08C9 "derived-zero point-neighborhood null homotopy"]
theorem at_of_derived_zero
    {E F : _root_.CochainComplex (Modules X) ℤ}
    (hE : _root_.SheafOfModules.CochainComplex.IsStrictlyPerfect E)
    (α : E ⟶ F) (hα : DerivedCategory.Q.map α = 0) (x : X) :
    IsLocallyNullHomotopicAt α x := sorry

end NullHomotopy

end IsStrictlyPerfect

end AlgebraicGeometry.RingedSpace.CochainComplex
