module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ResidualSpace
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.RelationFiniteFibre
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Decent

/-!
# Residual spaces isomorphic to spectra of fields

A residual space at a point is isomorphic to the spectrum of a field exactly
when that point has a monomorphic field-valued representative.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsResidualSpace

/-- A residual space at a point is isomorphic to the spectrum of a field if and
only if the point is represented by a monomorphism from the spectrum of a field. -/
@[stacks 0H1R]
theorem exists_iso_spec_iff_existsMonoFieldValuedPoint {S : Scheme.{u}}
    {X Z : AlgebraicSpace S} {x : Points X} (ι : Z ⟶ X) [IsResidualSpace ι x] :
    (∃ (k : Type u) (_ : Field k) (σ : Spec (.of k) ⟶ S),
        Nonempty (Z ≅ ofOver (Over.mk σ))) ↔
      existsMonoFieldValuedPoint X x :=
  sorry

/-- Every residual space of a decent algebraic space is isomorphic to the
spectrum of a field. -/
@[stacks 0H1R]
theorem exists_iso_spec_of_isDecent {S : Scheme.{u}} {X Z : AlgebraicSpace S}
    [IsDecent X] {x : Points X} (ι : Z ⟶ X) [IsResidualSpace ι x] :
    ∃ (k : Type u) (_ : Field k) (σ : Spec (.of k) ⟶ S),
      Nonempty (Z ≅ ofOver (Over.mk σ)) := by
  obtain ⟨p, _, hmono, hx⟩ := IsDecent.exists_quasiCompact_mono (X := X) x
  exact (exists_iso_spec_iff_existsMonoFieldValuedPoint ι).mpr ⟨p, hmono, hx⟩

end AlgebraicGeometry.AlgebraicSpace.IsResidualSpace
