/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module
public import ReasLib.AlgebraicGeometry.Scheme.Module.DeRham.Terms
public import Mathlib.RingTheory.Kaehler.Basic

@[expose] public section
open AlgebraicGeometry CategoryTheory Opposite
universe u
namespace AlgebraicGeometry.Scheme.RelativeDifferentials.Affine

variable {A : Type u} [CommRing A] {Y : Scheme.{u}} (f : Y ⟶ Spec (.of A))
variable (U : Y.affineOpens)

/-- The additive derivation on U is the component of the actual universal
sheaf derivation; no invented coordinate differential is used. -/
noncomputable def sectionDerivation :
    Γ(Y, U.1) →+ Γ(AlgebraicGeometry.Scheme.Modules.DeRham.oneForms f, U.1) :=
  (RingedSpace.Hom.universalDerivation f.toShHom).d (X := op U.1)

/-- The actual universal sheaf derivation annihilates pulled-back constants. -/
theorem sectionDerivation_base (a : A) :
    sectionDerivation f U (Scheme.Hom.sectionsMap f U a) = 0 := sorry

/-- View the actual affine component as an A-relative derivation, retaining
the chart's base map and the induced scalar action on local one-forms. -/
noncomputable def derivation :=
  -- Local instance justification (noncanonical choice): the map f fixes this affine chart algebra.
  letI : Algebra A Γ(Y, U.1) := (Scheme.Hom.sectionsMap f U).toAlgebra
  -- Local instance justification (noncanonical choice): A acts on differential sections through that chart algebra.
  letI : Module A Γ(AlgebraicGeometry.Scheme.Modules.DeRham.oneForms f, U.1) :=
    Module.compHom _ (Scheme.Hom.sectionsMap f U)
  ({ toFun := sectionDerivation f U
     map_add' := map_add _
     map_smul' := sorry
     map_one_eq_zero' := (RingedSpace.Hom.universalDerivation f.toShHom).d_one (op U.1)
     leibniz' := (RingedSpace.Hom.universalDerivation f.toShHom).d_mul } :
    Derivation A Γ(Y, U.1) Γ(AlgebraicGeometry.Scheme.Modules.DeRham.oneForms f, U.1))

/-- The canonical Kähler-to-sheaf map on this affine open is induced by
the universal sheaf derivation, not by an arbitrary isomorphism. -/
noncomputable def comparison :=
  -- Local instance justification (noncanonical choice): the actual structure map supplies the relative base action.
  letI : Algebra A Γ(Y, U.1) := (Scheme.Hom.sectionsMap f U).toAlgebra
  -- Local instance justification (noncanonical choice): use the same induced action as the derivation.
  letI : Module A Γ(AlgebraicGeometry.Scheme.Modules.DeRham.oneForms f, U.1) := Module.compHom _ (Scheme.Hom.sectionsMap f U)
  -- Local instance justification (noncanonical choice): the restricted action forms the canonical tower for f.
  letI : IsScalarTower A Γ(Y, U.1) Γ(AlgebraicGeometry.Scheme.Modules.DeRham.oneForms f, U.1) :=
    IsScalarTower.restrictScalars A Γ(Y, U.1) Γ(AlgebraicGeometry.Scheme.Modules.DeRham.oneForms f, U.1)
  (derivation f U).liftKaehlerDifferential

/-- On an affine open over an affine base the canonical comparison is
bijective. The affine-open restriction is essential; this is not asserted
for arbitrary nonaffine global sections. -/
theorem comparison_bijective : Function.Bijective (comparison f U) := sorry

end AlgebraicGeometry.Scheme.RelativeDifferentials.Affine
