module
public import stacks_project.Chap60.Remark_60_24_11_Comparison_DeRham
public import Mathlib.RingTheory.Kaehler.Basic

@[expose] public section
open AlgebraicGeometry CategoryTheory Opposite
universe u
namespace CrystallineAffineDifferentials

variable {A : Type u} [CommRing A] {Y : Scheme.{u}} (f : Y ⟶ Spec (.of A))
variable (U : Y.affineOpens)

/-- The ring map from A to the actual affine-open functions. -/
noncomputable abbrev baseMap : A →+* Γ(Y, U.1) :=
  (f.appLE ⊤ U.1 le_top).hom.comp (Scheme.ΓSpecIso (.of A)).inv.hom

/-- The additive derivation on U is the component of the actual universal
sheaf derivation; no invented coordinate differential is used. -/
noncomputable def sectionDerivation :
    Γ(Y, U.1) →+ Γ(CrystallineSmoothLiftTerms.oneForms f, U.1) :=
  (RingedSpace.Hom.universalDerivation f.toShHom).d (X := op U.1)

/-- The actual universal sheaf derivation annihilates pulled-back constants. -/
theorem sectionDerivation_base (a : A) :
    sectionDerivation f U (baseMap f U a) = 0 := sorry

/-- View the actual affine component as an A-relative derivation, retaining
the chart's base map and the induced scalar action on local one-forms. -/
noncomputable def derivation :=
  -- Local instance justification (noncanonical choice): the map f fixes this affine chart algebra.
  letI : Algebra A Γ(Y, U.1) := (baseMap f U).toAlgebra
  -- Local instance justification (noncanonical choice): A acts on differential sections through that chart algebra.
  letI : Module A Γ(CrystallineSmoothLiftTerms.oneForms f, U.1) :=
    Module.compHom _ (baseMap f U)
  ({ toFun := sectionDerivation f U
     map_add' := map_add _
     map_smul' := sorry
     map_one_eq_zero' := (RingedSpace.Hom.universalDerivation f.toShHom).d_one (op U.1)
     leibniz' := (RingedSpace.Hom.universalDerivation f.toShHom).d_mul } :
    Derivation A Γ(Y, U.1) Γ(CrystallineSmoothLiftTerms.oneForms f, U.1))

/-- The canonical Kähler-to-sheaf map on this affine open is induced by
the universal sheaf derivation, not by an arbitrary isomorphism. -/
noncomputable def comparison :=
  -- Local instance justification (noncanonical choice): the actual structure map supplies the relative base action.
  letI : Algebra A Γ(Y, U.1) := (baseMap f U).toAlgebra
  -- Local instance justification (noncanonical choice): use the same induced action as the derivation.
  letI : Module A Γ(CrystallineSmoothLiftTerms.oneForms f, U.1) := Module.compHom _ (baseMap f U)
  -- Local instance justification (noncanonical choice): the restricted action forms the canonical tower for f.
  letI : IsScalarTower A Γ(Y, U.1) Γ(CrystallineSmoothLiftTerms.oneForms f, U.1) :=
    IsScalarTower.restrictScalars A Γ(Y, U.1) Γ(CrystallineSmoothLiftTerms.oneForms f, U.1)
  (derivation f U).liftKaehlerDifferential

/-- On an affine open over an affine base the canonical comparison is
bijective. The affine-open restriction is essential; this is not asserted
for arbitrary nonaffine global sections. -/
theorem comparison_bijective : Function.Bijective (comparison f U) := sorry

end CrystallineAffineDifferentials
