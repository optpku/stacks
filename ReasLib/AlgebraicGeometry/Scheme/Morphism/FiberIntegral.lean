module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.FieldTheory.SeparableDegree
public import Mathlib.Order.Filter.TendstoCofinite
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ResidueField

/-!
# Fibre integrals of integer-valued functions

This module defines the separable-degree-weighted sum of an integer-valued
function over the finite fibres of a scheme morphism.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The fibre integral of `w : X → ℤ` along a scheme morphism with finite fibres,
weighted by the separable degrees of the residue-field extensions. -/
noncomputable def fiberIntegral {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : Filter.TendstoCofinite (fun x : X ↦ f x)) (w : X → ℤ) : Y → ℤ :=
  @Filter.TendstoCofinite.mapDomain X Y ℤ (fun x : X ↦ f x) _ hf
    (fun x ↦ w x * (Field.finSepDegree (Y.residueField (f x)) (X.residueField x) : ℤ))

/-- The fibre integral is the finite sum of the weighted separable degrees over a
point fibre. -/
theorem fiberIntegral_apply {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : Filter.TendstoCofinite (fun x : X ↦ f x)) (w : X → ℤ) (y : Y) :
    f.fiberIntegral hf w y =
      ((Filter.tendstoCofinite_iff_finite_preimage_singleton (fun x : X ↦ f x)).mp hf y).toFinset.sum
        (fun x ↦ w x *
          (Field.finSepDegree (Y.residueField (f x)) (X.residueField x) : ℤ)) := sorry

end AlgebraicGeometry.Scheme.Hom
