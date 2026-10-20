/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Cohomology.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pushforward.RightAdjoint
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.StructureSheaf

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped ENat

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/-- Proper pushforward to the spectrum of a field has the chosen right adjoint used by the
proper dualizing-complex construction. -/
noncomputable instance properPushforwardIsLeftAdjoint
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] :
    (pushforwardCohomologyIn f).IsLeftAdjoint :=
  @pushforwardIsLeftAdjoint X (Spec (CommRingCat.of k)) f
    (QuasiCompact.compactSpace_of_compactSpace f)
    (quasiSeparatedSpace_of_quasiSeparated f) inferInstance inferInstance

/-- The chosen dualizing complex of a proper scheme over a field, obtained by applying the
chosen right adjoint of derived pushforward to the derived structure sheaf of the base. -/
noncomputable def properDualizingComplex
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] : DerivedQCoh X :=
  (pushforwardCohomologyIn f).rightAdjoint.obj (structureSheaf (Spec (CommRingCat.of k)))

/-- The chosen proper dualizing complex is the right-adjoint image of the base structure
sheaf. -/
theorem properDualizingComplex_obj
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] :
    properDualizingComplex f =
      (pushforwardCohomologyIn f).rightAdjoint.obj (structureSheaf (Spec (CommRingCat.of k))) :=
  rfl

namespace ProperDualizingComplex

/-- The canonical comparison from the chosen right adjoint to any explicitly supplied right
adjoint of derived pushforward. -/
noncomputable def isoOfAdjunction
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (a : DerivedQCoh (Spec (CommRingCat.of k)) ⥤ DerivedQCoh X)
    (ha : pushforwardCohomologyIn f ⊣ a) :
    properDualizingComplex f ≅ a.obj (structureSheaf (Spec (CommRingCat.of k))) :=
  ((Adjunction.ofIsLeftAdjoint (pushforwardCohomologyIn f)).rightAdjointUniq ha).app
    (structureSheaf (Spec (CommRingCat.of k)))

/-- The canonical Krull-dimension index used for the dualizing module. -/
def dimensionIndex
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) : ℕ :=
  ((topologicalKrullDim X).unbotD 0).toNat

/-- The dimension index is the natural-number realization of the topological Krull dimension,
with the standard empty-space fallback. -/
theorem dimensionIndex_def
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) :
    dimensionIndex f = ((topologicalKrullDim X).unbotD 0).toNat :=
  rfl

/-- The dualizing module is the bottom-degree cohomology sheaf of the chosen proper dualizing
complex. -/
noncomputable def dualizingModule
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] : X.Modules :=
  RingedSpace.ModuleDerived.cohomologySheaf (properDualizingComplex f).obj
    (-(dimensionIndex f : ℤ))

/-- The dualizing module is the degree `-dimensionIndex f` cohomology sheaf. -/
theorem dualizingModule_eq
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] :
    dualizingModule f =
      RingedSpace.ModuleDerived.cohomologySheaf (properDualizingComplex f).obj
        (-(dimensionIndex f : ℤ)) :=
  rfl

end ProperDualizingComplex
end AlgebraicGeometry.Scheme.DerivedQCoh
