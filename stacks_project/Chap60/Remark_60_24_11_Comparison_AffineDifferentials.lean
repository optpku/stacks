/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module
public import ReasLib.AlgebraicGeometry.Scheme.Module.Differentials.Affine
public import stacks_project.Chap60.Remark_60_24_11_Comparison_DeRham

@[expose] public section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
namespace CrystallineAffineDifferentials
variable {A : Type u} [CommRing A] {Y : Scheme.{u}} (f : Y ⟶ Spec (.of A))
variable (U : Y.affineOpens)
/-- The affine-open specialization of the structure morphism's map on sections. -/
noncomputable abbrev baseMap : A →+* Γ(Y, U.1) := Scheme.Hom.sectionsMap f U.1
export AlgebraicGeometry.Scheme.RelativeDifferentials.Affine (sectionDerivation sectionDerivation_base derivation comparison comparison_bijective)
#check (AlgebraicGeometry.Scheme.RelativeDifferentials.Affine.sectionDerivation f U :
  Γ(Y, U.1) →+ Γ(AlgebraicGeometry.Scheme.Modules.DeRham.oneForms f, U.1))
end CrystallineAffineDifferentials
