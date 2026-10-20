/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.VanishingCycles.StalkCompatibility
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Torsion
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

@[expose] public section

open CategoryTheory CategoryTheory.Sheaf AlgebraicGeometry
open AlgebraicGeometry.Scheme.EtaleVanishingCycles

universe u

namespace AlgebraicGeometry.Scheme.Etale

/-- For a proper morphism locally acyclic relative to bounded-below étale coefficients
with torsion cohomology, specialization on geometric stalks of the derived direct image
is an isomorphism. -/
theorem isIso_derivedPushforward_specializationMap
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] (s t : GeometricPoint S)
    (point : Spec (.of t.K) ⟶ strictHenselizationAt S s)
    (point_over : point ≫ StrictHenselization.toScheme S s = t.hom)
    (K : DerivedCategory.Plus (Coefficients X)) [LocallyAcyclicRelative f K.obj]
    (hTorsion : DerivedCategory.cohomologyIn
      (IsLocallyTorsion : ObjectProperty (Coefficients X)) K.obj) :
    IsIso (derivedPushforward_specializationMap f s t point point_over K.obj) := sorry

/-- Torsion cohomology supplied through `Fact` makes geometric-stalk specialization
of a proper locally acyclic derived direct image invertible. -/
instance isIso_derivedPushforward_specializationMap_of_fact
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] (s t : GeometricPoint S)
    (point : Spec (.of t.K) ⟶ strictHenselizationAt S s)
    (point_over : point ≫ StrictHenselization.toScheme S s = t.hom)
    (K : DerivedCategory.Plus (Coefficients X)) [LocallyAcyclicRelative f K.obj]
    [Fact (DerivedCategory.cohomologyIn
      (IsLocallyTorsion : ObjectProperty (Coefficients X)) K.obj)] :
    IsIso (derivedPushforward_specializationMap f s t point point_over K.obj) :=
  isIso_derivedPushforward_specializationMap f s t point point_over K Fact.out

namespace Cohomology

/-- For a proper morphism locally acyclic relative to bounded-below étale coefficients
with torsion cohomology, cospecialization from the geometric fibre at the generizing point
to the geometric fibre at the specializing point is an isomorphism. -/
theorem isIso_cospecialization
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] (s t : GeometricPoint S)
    (point : Spec (.of t.K) ⟶ strictHenselizationAt S s)
    (point_over : point ≫ StrictHenselization.toScheme S s = t.hom)
    (K : DerivedCategory.Plus (Coefficients X)) [LocallyAcyclicRelative f K.obj]
    (hTorsion : DerivedCategory.cohomologyIn
      (IsLocallyTorsion : ObjectProperty (Coefficients X)) K.obj) :
    IsIso (cospecialization f s t point point_over K) := sorry

/-- Torsion cohomology supplied through `Fact` makes geometric-fibre cospecialization
for a proper locally acyclic morphism invertible on bounded-below coefficients. -/
instance isIso_cospecialization_of_fact
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] (s t : GeometricPoint S)
    (point : Spec (.of t.K) ⟶ strictHenselizationAt S s)
    (point_over : point ≫ StrictHenselization.toScheme S s = t.hom)
    (K : DerivedCategory.Plus (Coefficients X)) [LocallyAcyclicRelative f K.obj]
    [Fact (DerivedCategory.cohomologyIn
      (IsLocallyTorsion : ObjectProperty (Coefficients X)) K.obj)] :
    IsIso (cospecialization f s t point point_over K) :=
  isIso_cospecialization f s t point point_over K Fact.out

end Cohomology

end AlgebraicGeometry.Scheme.Etale
