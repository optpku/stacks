module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.ResidueField

/-!
# Residue-field point coproducts

This module defines the coproduct of the spectra of the residue fields at a specified set of
points of a scheme, together with its canonical morphism to the scheme.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry

/-- The coproduct of the spectra of the residue fields of the points of `E ⊆ X`. -/
noncomputable def pointSpectrumCoproduct (X : Scheme.{u}) (E : Set X) : Scheme.{u} :=
  ∐ fun x : E ↦ Spec (X.residueField x.1)

/-- The canonical morphism from the coproduct of the residue-field spectra over `E` to `X`. -/
noncomputable def pointSpectrumCoproductTo (X : Scheme.{u}) (E : Set X) :
    pointSpectrumCoproduct X E ⟶ X :=
  Limits.Sigma.desc (fun x : E ↦ X.fromSpecResidueField x.1)

/-- The residue-field point coproduct morphism is the descent map of its canonical legs. -/
theorem pointSpectrumCoproductTo_def (X : Scheme.{u}) (E : Set X) :
    pointSpectrumCoproductTo X E =
      Limits.Sigma.desc (fun x : E ↦ X.fromSpecResidueField x.1) := rfl

/-- The `x`-th leg of the residue-field point coproduct morphism is the canonical morphism
from the spectrum of the residue field at `x`. -/
@[simp, reassoc]
theorem pointSpectrumCoproductTo_ι (X : Scheme.{u}) (E : Set X) (x : E) :
    Limits.Sigma.ι
        (fun x : E ↦
          Spec (X.residueField x.1)) x ≫
      pointSpectrumCoproductTo X E =
        X.fromSpecResidueField x.1 := by
  simpa [pointSpectrumCoproductTo_def] using
    (Limits.Sigma.ι_desc (fun x : E ↦ X.fromSpecResidueField x.1) x)

end AlgebraicGeometry

end
